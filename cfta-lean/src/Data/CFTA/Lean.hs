{-# LANGUAGE OverloadedStrings #-}

{- | Fits checked inside Lean's elaborator: Hectare proposes programs, and a
walk in Lean's @MetaM@ checks them.

The checker is the oracle of @cfta-lean/oracle@, a Lean program that
runs as a child process and speaks a line protocol on its standard input and
output ("Oracle.Session" on the Lean side). The work splits so:

* Lean erases the types of a library of constants and of a goal's arguments
  to Hectare's first-order types ('library', 'enterGoal').
* Hectare proposes programs over the erased leaves, and the walk of
  "Data.CFTA.Gen.Synthesis.Walk" keeps the trie of dead prefixes and the
  prefix of the last program ('streamFits').
* Lean checks each program from the kept prefix on, in one round trip: it
  restores the @MetaM@ state before the first token that goes, steps the
  rest, and checks the complete program.
* The modes ('optionModes') run in order as a portfolio
  ("Data.CFTA.Gen.Synthesis.Portfolio") with this checker: Hectare's
  programs (mode (a), the default), or the search over states of
  "Data.CFTA.Gen.Synthesis.States" (mode (b)), whose goals are Lean's: the
  oracle refines a goal in one round trip, and every constant of the
  library is a leaf, also one without a Hectare type.
-}
module Data.CFTA.Lean (
    -- * Oracles
    Oracle,
    withOracle,
    handleOracle,
    oracleImportMilliseconds,

    -- * Libraries and goals
    Component (..),
    library,
    receiveLibrary,
    Goal (..),
    enterGoal,
    receiveGoal,

    -- * Fits
    Options (..),
    Mode (..),
    defaultOptions,
    Statistics (..),
    streamFits,
    configureChecks,
    lastTerm,

    -- * States from goals
    searchStates,
    features,
    suggest,

    -- * Measurements
    ping,
    counters,
    search,
    snapshots,
) where

import Control.Exception (bracket)
import Control.Monad (void)
import Data.Bifunctor (first)
import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)
import System.Directory (makeAbsolute)
import System.IO (BufferMode (LineBuffering), Handle, hClose, hFlush, hSetBuffering, hSetEncoding, utf8)
import System.Process (
    CreateProcess (..),
    StdStream (CreatePipe),
    createProcess,
    proc,
    terminateProcess,
    waitForProcess,
 )

import Data.CFTA.Gen.Synthesis (Type, parseType)
import Data.CFTA.Gen.Synthesis.Portfolio (Run (..), combined, hectare, portfolio, states)
import Data.CFTA.Gen.Synthesis.States (Figures, Goals (..), Refinement (..))
import Data.CFTA.Gen.Synthesis.Walk (
    Checker (..),
    Erased (..),
    Extension (..),
    Fit,
    Limits (..),
    Progress (..),
    Token,
 )
import qualified Data.CFTA.Gen.Synthesis.Walk as Walk

-- Oracles

-- | A running oracle: the pipes to it and the time of its import.
data Oracle = Oracle
    { oracleInput :: Handle
    , oracleOutput :: Handle
    , oracleImportMilliseconds :: Int
    -- ^ The time that the oracle took to import its modules.
    }

{- | Run the oracle of the Lake project in the directory, with the modules to
import (@Init@ when there are none), for the function. The oracle runs in the
project's directory, so that its toolchain is the project's.
-}
withOracle :: FilePath -> [String] -> (Oracle -> IO a) -> IO a
withOracle relative modules use = bracket start stop $ \(input, output, _) -> do
    ready <- receiveFrom output
    case ready of
        ["ready", milliseconds] -> use (Oracle input output (read (Text.unpack milliseconds)))
        other -> fail ("lean-oracle: " <> show other)
  where
    start = do
        directory <- makeAbsolute relative
        (Just input, Just output, _, process) <-
            createProcess
                (proc (directory <> "/.lake/build/bin/lean-oracle") modules)
                    { cwd = Just directory
                    , std_in = CreatePipe
                    , std_out = CreatePipe
                    }
        mapM_ (`hSetEncoding` utf8) [input, output]
        hSetBuffering input LineBuffering
        pure (input, output, process)
    stop (input, _, process) = do
        hClose input
        terminateProcess process
        _ <- waitForProcess process
        pure ()

{- | An oracle on two handles: the first for the requests, the second for the
replies. A program that a Lean tactic runs as its proposer is the client of
the tactic on its standard output and input.
-}
handleOracle :: Handle -> Handle -> Oracle
handleOracle input output = Oracle input output 0

-- | Write a request.
send :: Oracle -> [Text] -> IO ()
send oracle fields = do
    Text.hPutStrLn (oracleInput oracle) (Text.intercalate "\t" fields)
    hFlush (oracleInput oracle)

-- | Read a reply.
receive :: Oracle -> IO [Text]
receive = receiveFrom . oracleOutput

-- | Read a reply from a handle.
receiveFrom :: Handle -> IO [Text]
receiveFrom handle = Text.splitOn "\t" <$> Text.hGetLine handle

-- | Read the lines of a reply up to its @end@ line.
block :: Oracle -> IO [[Text]]
block oracle = do
    fields <- receive oracle
    case fields of
        "end" : _ -> pure []
        _ -> (fields :) <$> block oracle

-- Libraries and goals

-- | A leaf of the oracle: its name, its index in the protocol, and its erased type.
data Component = Component
    { componentName :: Text
    , componentIndex :: Int
    , componentType :: Type
    }
    deriving (Eq, Show)

{- | Erase the constants of a library: each item is a constant, or @N.*@ for
the definitions and constructors of the namespace @N@. The result has the
components with a Hectare type, and the other constants with the reason.
-}
library :: Oracle -> [Text] -> IO ([Component], [(Text, Text)])
library oracle items = send oracle ("library" : items) >> receiveLibrary oracle

{- | Read the lines of a library up to @end@: the components, and the other
constants with the reason.
-}
receiveLibrary :: Oracle -> IO ([Component], [(Text, Text)])
receiveLibrary oracle = do
    lines' <- block oracle
    pure
        ( mapMaybe component lines'
        , [(name, reason) | "skipped" : name : reason : _ <- lines']
        )

-- | A component line of a reply.
component :: [Text] -> Maybe Component
component fields = case fields of
    [kind, index, name, typ]
        | kind `elem` ["component", "argument"]
        , Right parsed <- parseType typ ->
            Just (Component name (read (Text.unpack index)) parsed)
    _ -> Nothing

-- | A goal: its explicit arguments, its erased type, and the oracle's errors.
data Goal = Goal
    { goalArguments :: [Component]
    , goalType :: Maybe Type
    , goalErrors :: [Text]
    }
    deriving (Eq, Show)

{- | Elaborate a goal type in Lean syntax, as @∀ {α : Type} [BEq α] (x : α)
(xs : List α), Bool@, and enter its binders. After this the oracle checks
programs of this goal.
-}
enterGoal :: Oracle -> Text -> IO Goal
enterGoal oracle text = send oracle ["goal", text] >> receiveGoal oracle

-- | Read the lines of a goal up to @end@: its arguments, its erased type, and the errors.
receiveGoal :: Oracle -> IO Goal
receiveGoal oracle = do
    lines' <- block oracle
    pure
        Goal
            { goalArguments = [argument | fields@("argument" : _) <- lines', Just argument <- [component fields]]
            , goalType = case [typ | ["goal", typ] <- lines'] of
                typ : _ -> either (const Nothing) Just (parseType typ)
                [] -> Nothing
            , goalErrors = [message | "error" : message : _ <- lines']
            }

-- Fits

-- | The options of a search.
data Options = Options
    { optionMaximumSize :: Int
    -- ^ The largest program, in leaves.
    , optionArgumentOnly :: [Text]
    -- ^ The components that only appear as an argument, as @id@.
    , optionAvoid :: [([Text], Maybe [Text])]
    -- ^ Hectare's pruning rules for programs of size two.
    , optionDeadline :: Maybe Word64
    -- ^ A time on the monotonic clock, in nanoseconds, to stop at.
    , optionModes :: [(Mode, Maybe Double)]
    {- ^ The modes, in the order of the portfolio, each with its budget in
    seconds ('Nothing': the rest of the time). A mode runs when the one
    before it did not end the search.
    -}
    , optionReport :: Maybe (Int -> Progress -> IO ())
    -- ^ A function to call after each size.
    }

-- | A way to propose the programs of a goal.
data Mode
    = -- | Hectare's programs over the erased components (mode (a)).
      Hectare
    | -- | The programs of states of Lean's own goals (mode (b)).
      States
    deriving (Eq, Show, Read)

-- | Programs of up to five leaves, mode (a) alone, no other limit.
defaultOptions :: Options
defaultOptions = Options 5 [] [] Nothing [(Hectare, Nothing)] Nothing

-- | The figures of a search on the Haskell side.
data Statistics = Statistics
    { statisticsProgress :: !Progress
    , statisticsExtensions :: !Int
    -- ^ The round trips to the oracle.
    , statisticsRoundTripNanos :: !Word64
    -- ^ The time of the round trips, with the oracle's work.
    , statisticsRuns :: [Run]
    -- ^ The runs of the modes, in order; the progress above is their sum.
    , statisticsStates :: Maybe Figures
    -- ^ The figures of the states of mode (b), when it ran.
    }
    deriving (Eq, Show)

{- | Check the programs of the modes ('optionModes') over the components and
the goal's arguments, in their orders (Hectare's enumeration order for mode
(a)), and call the function on each fit; stop when it returns 'False', or at
the limits. The round trips counted are those of the checks.
-}
streamFits :: Oracle -> Options -> [Component] -> Goal -> (Fit -> IO Bool) -> IO Statistics
streamFits oracle options components goal accept = do
    kept <- newIORef 0
    trips <- newIORef (0, 0)
    figures <- newIORef Nothing
    -- Mode (b) has every leaf of the protocol, also the constants without a Hectare type.
    protocol <-
        if States `elem` map fst (optionModes options)
            then Just <$> protocolGoals oracle (optionMaximumSize options)
            else pure Nothing
    let indices = maybe (leafIndices components goal) (\(names, _, _) -> Map.fromList (zip names [0 ..])) protocol
        extend tokens = do
            start <- getMonotonicTimeNSec
            held <- readIORef kept
            let known = takeWhile ((`Map.member` indices) . fst) tokens
            send oracle ("extend" : tshow held : [tshow (indices Map.! name) <> ":" <> tshow children | (name, children) <- known])
            reply <- receive oracle
            end <- getMonotonicTimeNSec
            modifyIORef' trips (\(count, nanos) -> (count + 1, nanos + end - start))
            case reply of
                ["died", index] -> pure (Died (read (Text.unpack index)))
                "done" : fits : _
                    | length known < length tokens -> pure (Died (held + length known))
                    | otherwise -> pure (Done (fits == "1"))
                other -> fail ("lean-oracle: " <> show other)
        checker = Checker (writeIORef kept) extend
        onSize size progress = mapM_ (\report -> report size progress) (optionReport options)
        limits = Limits (optionMaximumSize options) Nothing (optionDeadline options)
        proposer (mode, budget) = case mode of
            Hectare -> hectare "hectare" budget checker onSize (\_ _ -> pure ()) leaves (optionAvoid options) <$> goalType goal
            States ->
                ( \(names, required, root) ->
                    states
                        "states"
                        budget
                        checker
                        onSize
                        (\_ _ -> pure ())
                        (writeIORef figures . Just)
                        (Goals names required root (refinements oracle (optionMaximumSize options)))
                        (optionAvoid options)
                )
                    <$> protocol
    runs <- portfolio limits (mapMaybe proposer (optionModes options)) accept
    (count, nanos) <- readIORef trips
    Statistics (combined runs) count nanos runs <$> readIORef figures
  where
    leaves =
        [ Erased
            (componentName c)
            (componentType c)
            (if componentName c `elem` optionArgumentOnly options then Walk.ArgumentOnly else Walk.Component)
        | c <- components
        ]
            <> [Erased (componentName c) (componentType c) Walk.Required | c <- goalArguments goal]

{- | Start the generic search over states on the oracle's goal, for programs
up to a size: the names of the leaves of the protocol by index, the indices
of the required ones (the goal's arguments), and the key of the goal.
-}
protocolGoals :: Oracle -> Int -> IO ([Text], [Int], Int)
protocolGoals oracle size = do
    send oracle ["goals", tshow size]
    lines' <- blockWith oracle
    let leaves = [(read (Text.unpack index), name, required == "1") | ["leaf", index, name, required] <- fst lines']
    pure ([name | (_, name, _) <- leaves], [index | (index, _, True) <- leaves], snd lines')

-- | Read the lines of a reply up to its @end <number>@ line, and the number.
blockWith :: Oracle -> IO ([[Text]], Int)
blockWith oracle = do
    fields <- receive oracle
    case fields of
        ["end", number] -> pure ([], read (Text.unpack number))
        _ -> first (fields :) <$> blockWith oracle

{- | The refinements of the goal of a key for numbers of children below a
bound, in one round trip: each leaf whose step passes, with its number of
children and the keys of its child goals, in the oracle's order (by leaf,
then by number of children); 'Nothing' when the deadline comes first.
-}
refinements :: Oracle -> Int -> Maybe Word64 -> Int -> [Int] -> IO (Maybe [Refinement Int])
refinements oracle bound deadline key counts = do
    now <- getMonotonicTimeNSec
    let milliseconds = maybe (10 ^ (9 :: Int)) (\end -> if end > now then fromIntegral ((end - now) `div` 1000000) else 0) deadline :: Int
    send oracle (["transitions", tshow milliseconds, tshow key] <> map tshow counts)
    fields <- receive oracle
    case fields of
        ["timeout"] -> pure Nothing
        "transitions" : found -> pure (Just (map refinement found))
        other -> fail ("lean-oracle: " <> show other)
  where
    refinement field = case Text.splitOn ":" field of
        [leaf, k, children] ->
            Refinement
                (number leaf * bound + number k)
                (number leaf)
                (number k)
                (if Text.null children then [] else map number (Text.splitOn "," children))
        _ -> error ("lean-oracle: a bad refinement " <> show field)
    number = read . Text.unpack

{- | Turn on optional levels of the cascade of the oracle's step: @head@
compares the heads of the leaf's result type and the goal type before
@isDefEq@, and @synthEnd@ leaves @synthInstance?@ to the complete program.
The other levels (the arity, @isDefEq@, and the complete check) are always
on.
-}
configureChecks :: Oracle -> [Text] -> IO ()
configureChecks oracle checks = send oracle ("checks" : checks) >> void (receive oracle)

-- | The index in the protocol of each leaf: the components and the goal's arguments.
leafIndices :: [Component] -> Goal -> Map Text Int
leafIndices components goal = Map.fromList [(componentName c, componentIndex c) | c <- components <> goalArguments goal]

{- | The search over states that Lean builds from its own goals, without
Hectare and without erasure: size by size up to the bound, until it finds the
expected program (its tokens) or the seconds pass. Its leaves are every
constant of the library, also the ones without a Hectare type. The result has
the oracle's figures by name.
-}
searchStates :: Oracle -> Int -> Int -> [Token] -> IO (Map Text Text)
searchStates oracle bound seconds expected = do
    send oracle ("states" : tshow bound : tshow seconds : [name <> ":" <> tshow children | (name, children) <- expected])
    fields <- receive oracle
    pure $
        Map.fromList
            [ (key, value)
            | field <- drop 1 fields
            , let (key, rest) = Text.breakOn "=" field
            , Just value <- [Text.stripPrefix "=" rest]
            ]

{- | The features of the goal that predict which mode solves it, for programs
up to a size: whether the query or a leaf that fits the goal has a
higher-kinded variable or a class over a type constructor, and the leaves
that fit with a child goal that stays open. The result has the oracle's
figures by name.
-}
features :: Oracle -> Int -> IO (Map Text Text)
features oracle bound = do
    send oracle ["features", tshow bound]
    fields <- receive oracle
    pure $
        Map.fromList
            [ (key, value)
            | field <- drop 1 fields
            , let (key, rest) = Text.breakOn "=" field
            , Just value <- [Text.stripPrefix "=" rest]
            ]

{- | The portfolio of @hectare?@ on the goal, with its own leaves (the goal's
arguments, the namespaces of its types, and general functions), up to a
size: mode (a) for the budget in seconds (with the proposer of the oracle's
variable @HECTARE_PROPOSER@), then the search over states; until it finds the
expected program (its tokens), a count of fits, or the seconds pass. The flag
requires every argument in a fit. The result has the oracle's figures by
name: the expected program's rank among the fits, the mode that found it,
the fits, the outcome and time of each run, and the first fit.
-}
suggest :: Oracle -> Int -> Int -> Int -> Bool -> Int -> [Token] -> IO (Map Text Text)
suggest oracle size count seconds useAll budget expected = do
    send oracle $
        ["suggest", tshow size, tshow count, tshow seconds, if useAll then "1" else "0", tshow budget]
            <> [name <> ":" <> tshow children | (name, children) <- expected]
    fields <- receive oracle
    pure $
        Map.fromList
            [ (key, value)
            | field <- drop 1 fields
            , let (key, rest) = Text.breakOn "=" field
            , Just value <- [Text.stripPrefix "=" rest]
            ]

-- | The last program that fit, as Lean prints it.
lastTerm :: Oracle -> IO Text
lastTerm oracle = do
    send oracle ["term"]
    fields <- receive oracle
    pure (Text.intercalate "\t" (drop 1 fields))

-- Measurements

-- | One round trip without work.
ping :: Oracle -> IO ()
ping oracle = send oracle ["ping"] >> void (receive oracle)

-- | The oracle's counters of the walk, by name.
counters :: Oracle -> IO (Map Text Integer)
counters oracle = do
    send oracle ["stats"]
    fields <- receive oracle
    pure $
        Map.fromList
            [ (key, read (Text.unpack value))
            | field <- drop 1 fields
            , let (key, rest) = Text.breakOn "=" field
            , Just value <- [Text.stripPrefix "=" rest]
            ]

{- | @exact?@ on the goal, with every argument required when the flag is
'True': the milliseconds, and the term that it found.
-}
search :: Oracle -> Bool -> IO (Int, Maybe Text)
search oracle required = do
    send oracle ["search", if required then "1" else "0"]
    fields <- receive oracle
    pure $ case fields of
        ["search", milliseconds, "1", term] -> (read (Text.unpack milliseconds), Just term)
        "search" : milliseconds : _ -> (read (Text.unpack milliseconds), Nothing)
        _ -> (0, Nothing)

-- | The nanoseconds of one pair of @saveState@ and @restore@, over so many pairs.
snapshots :: Oracle -> Int -> IO Int
snapshots oracle pairs = do
    send oracle ["snapshots", tshow pairs]
    fields <- receive oracle
    pure $ case fields of
        ["snapshots", nanos] -> read (Text.unpack nanos)
        _ -> 0

-- | A number as text.
tshow :: (Show a) => a -> Text
tshow = Text.pack . show
