{-# LANGUAGE OverloadedStrings #-}

{- | Hoogle+-like queries over Lean's core library, synthesized with
"Data.CFTA.Lean": Hectare proposes programs over constants that Lean erases,
and a walk in Lean's @MetaM@ checks them.

The library is a rung: @core@, about 70 constants of @List@, @Option@,
@Prod@, @Nat@, and @Bool@ and the class methods of the queries; or @sweep@,
every definition and constructor of the namespaces @List@, @Option@, @Nat@,
@Prod@, @Bool@, and @Function@, with the same class methods.

Each query runs in a child process with a time limit, and the child runs its
own oracle. A row gives the query, the rung, the outcome (@solved@, @other@
when other programs fit but not the expected one, @unsolved@, @timeout@, or
@crash@), the bound, the size of the first fit and of the expected one, the
programs that Hectare proposed, the programs under a dead prefix, the round
trips to the oracle, the oracle's steps and @synthInstance?@ calls and prunes,
the seconds, the oracle's import in milliseconds, the microseconds of a round
trip and of the oracle's work in it, the nanoseconds of a snapshot and of a
restore in the walk, the first fit, and Lean's term of the last fit.

> hectare-lean [RUNG [SECONDS [NAME...]]]
> hectare-lean --states RUNG SECONDS [NAME...]
> hectare-lean --query NAME RUNG SECONDS
> hectare-lean --states-query NAME RUNG SECONDS
> hectare-lean --search [NAME...]
> hectare-lean --suggest SECONDS BUDGET [NAME...]
> hectare-lean --portfolio RUNG SECONDS [NAME...]
> hectare-lean --portfolio-query NAME RUNG SECONDS
> hectare-lean --features RUNG [NAME...]
> hectare-lean --ping COUNT

@--portfolio@ runs mode (a) for a budget of @HECTARE_LEAN_BUDGET@ seconds
(2 by default), then, when it did not find the expected program, the search
over states with the index for the rest of the seconds.

@--states@ runs the search over states that Lean builds from its own goals
("Oracle.States" on the Lean side) instead of Hectare's programs, with the
same library, for the same expected program.

Each query also prints its cost cascade: a row @cascade@ for each level, with
the mode, the level, the rejections, the passes, the nanoseconds per
decision, and a note. The variable @HECTARE_LEAN_CHECKS@ turns on optional
levels of the oracle's step, separated by commas: @head@ (compare the heads
of the types before @isDefEq@), @synthEnd@ (call @synthInstance?@ only on the
complete program), and @index@ (look up the leaves of a new state in a
discrimination tree, for @--states@).

The variable @HECTARE_LEAN_MODES@ gives the modes of the portfolio of
"Data.CFTA.Lean" ('optionModes') for the default runs, separated by commas,
each with an optional budget in seconds after a colon: @hectare@ (mode (a),
the default), @states@ (the generic search over states, mode (b) of
"Data.CFTA.Gen.Synthesis.States", whose oracle requests are counted in its
figures), or @hectare:2,states@. Then a query also prints a row @run@ for
each run (the query, the mode, the outcome, the seconds, the programs, and
the fits) and a row @figures@ with the figures of the states.

@--search@ runs @exact?@ on each query, with every argument required (as
@exact? using@) and without, and prints its time and term. @--ping@ measures
a round trip without work and a pair of @saveState@ and @restore@. The
variable @CFTA_LEAN_ORACLE@ names the oracle's Lake project, by default
@cfta-lean/oracle@.
-}
module Main (main) where

import Control.Exception (SomeException, try)
import Control.Monad (forM_, replicateM_, when)
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isNothing)
import Data.Text (Text)
import qualified Data.Text as Text
import GHC.Clock (getMonotonicTime, getMonotonicTimeNSec)
import System.Environment (getArgs, getExecutablePath, lookupEnv)
import System.Exit (ExitCode (..))
import System.IO (hFlush, stdout)
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)
import Text.Printf (printf)
import Text.Read (readMaybe)

import Data.CFTA.Gen.Synthesis (Program (..), parseProgram, renderProgram)
import Data.CFTA.Gen.Synthesis.Portfolio (Run (..))
import Data.CFTA.Gen.Synthesis.Walk (Fit (..), Progress (..), preorder)
import Data.CFTA.Lean

main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        ["--query", name, rung, seconds] -> runQuery name rung (read seconds)
        ["--states-query", name, rung, seconds] -> runStatesQuery name rung (read seconds)
        "--states" : rung : seconds : names -> runSuite "--states-query" rung (read seconds) names
        "--search" : names -> runSearch names
        "--suggest" : seconds : budget : names -> runSuggest (read seconds) (read budget) names
        "--portfolio" : rung : seconds : names -> runSuite "--portfolio-query" rung (read seconds) names
        ["--portfolio-query", name, rung, seconds] -> runPortfolioQuery name rung (read seconds)
        "--features" : rung : names -> runFeatures rung names
        ["--ping", count] -> runPing (read count)
        [] -> runSuite "--query" "core" 60 []
        [rung] -> runSuite "--query" rung 60 []
        rung : seconds : names -> runSuite "--query" rung (read seconds) names

-- Queries

-- | A query: its name, its type in Lean syntax, and the expected program.
data LeanQuery = LeanQuery
    { queryName :: String
    , querySignature :: Text
    , querySolution :: Program
    }

-- | The queries.
queries :: [LeanQuery]
queries =
    [ query "firstOr" "∀ {α : Type} (xs : List α) (d : α), α" "List.headD xs d"
    , query "lookupOr" "∀ {α β : Type} [BEq α] (k : α) (d : β) (xs : List (α × β)), β" "Option.getD (List.lookup k xs) d"
    , query "countElem" "∀ {α : Type} [BEq α] (x : α) (xs : List α), Nat" "List.count x xs"
    , query "dedup" "∀ {α : Type} [BEq α] (xs : List α), List α" "List.eraseDups xs"
    , query "sumAll" "∀ {α : Type} [Add α] [Zero α] (xs : List α), α" "List.sum xs"
    , query "addPair" "∀ {α : Type} [Add α] (p : α × α), α" "Add.add (Prod.fst p) (Prod.snd p)"
    , query "maxPair" "∀ {α : Type} [Max α] (p : α × α), α" "Max.max (Prod.fst p) (Prod.snd p)"
    , query "compareLengths" "∀ {α : Type} (xs ys : List α), Ordering" "Ord.compare (List.length xs) (List.length ys)"
    , query "totalLength" "∀ {α : Type} (xss : List (List α)), Nat" "List.length (List.flatten xss)"
    , query "catOptions" "∀ {α : Type} (xs : List (Option α)), List α" "List.filterMap id xs"
    , query "applyN" "∀ {α : Type} (f : α → α) (n : Nat) (x : α), α" "Nat.repeat f n x"
    , query "takeDrop" "∀ {α : Type} (n m : Nat) (xs : List α), List α" "List.take m (List.drop n xs)"
    , query "allEqual" "∀ {α : Type} [BEq α] (x : α) (xs : List α), Bool" "List.all xs (BEq.beq x)"
    , query "firstJust" "∀ {α : Type} (d : α) (xs : List (Option α)), α" "Option.getD (List.head? (List.filterMap id xs)) d"
    , query "swapAll" "∀ {α β : Type} (ps : List (α × β)), List (β × α)" "List.map Prod.swap ps"
    , query "firstsOfZip" "∀ {α β : Type} (xs : List α) (ys : List β), List α" "List.map Prod.fst (List.zip xs ys)"
    , query "maxOrZero" "∀ (xs : List Nat), Nat" "Option.getD (List.max? xs) Nat.zero"
    , query "containsEither" "∀ {α : Type} [BEq α] (x : α) (xs ys : List α), Bool" "List.contains (List.append xs ys) x"
    , query "mapOr" "∀ {α β : Type} (f : α → β) (o : Option α) (d : β), β" "Option.getD (Option.map f o) d"
    , query "replicateN" "∀ {α : Type} (n : Nat) (x : α), List α" "List.replicate n x"
    , -- Two queries whose expected programs have no erased type: @+@ has a
      -- result of any type, and @Functor.map@ an applied type variable.
      query "addPairPlus" "∀ {α : Type} [Add α] (p : α × α), α" "HAdd.hAdd (Prod.fst p) (Prod.snd p)"
    , query "mapFunctor" "∀ {α β : Type} (f : α → β) (o : Option α), Option β" "Functor.map f o"
    ]
  where
    query name signature solution = LeanQuery name signature (either error id (parseProgram solution))

-- | The number of leaves of a program.
programSize :: Program -> Int
programSize program = case program of
    Var _ -> 1
    App function argument -> programSize function + programSize argument

-- Libraries

-- | The class methods and the functions on @Bool@ of both rungs.
methods :: [Text]
methods =
    [ "BEq.beq"
    , "Add.add"
    , "Mul.mul"
    , "Max.max"
    , "Min.min"
    , "Ord.compare"
    , "id"
    , "not"
    , "and"
    , "or"
    , "HAdd.hAdd"
    , "Functor.map"
    ]

-- | The items of a rung.
rungItems :: String -> [Text]
rungItems rung = case rung of
    "core" ->
        map ("List." <>) (Text.words listFunctions)
            <> map ("Option." <>) (Text.words "map getD get! isSome isNone toList bind some none")
            <> map ("Prod." <>) (Text.words "fst snd mk swap")
            <> map ("Nat." <>) (Text.words "succ add sub mul zero repeat")
            <> ["Bool.true", "Bool.false"]
            <> methods
    "sweep" -> ["List.*", "Option.*", "Nat.*", "Prod.*", "Bool.*", "Function.*"] <> methods
    _ -> error ("no rung " <> rung)
  where
    listFunctions =
        "map filter foldr foldl length append reverse head? headD getLast? getLastD tail take drop zip unzip \
        \zipWith lookup elem contains count all any sum replicate range filterMap flatten flatMap find? \
        \partition splitAt eraseDups insert max? min? isEmpty reduceOption cons nil takeWhile dropWhile idxOf"

-- | Hectare's pruning rule, with Lean's names: a list function is not applied to @[]@.
avoid :: [([Text], Maybe [Text])]
avoid =
    [
        ( map
            ("List." <>)
            ( Text.words
                "head? headD getLast? getLastD tail length reverse flatten sum max? min? isEmpty reduceOption eraseDups unzip"
            )
        , Just ["List.nil"]
        )
    ]

-- | The oracle's Lake project.
oracleDirectory :: IO FilePath
oracleDirectory = fromMaybe "cfta-lean/oracle" <$> lookupEnv "CFTA_LEAN_ORACLE"

-- Runs

-- | Find a query by name.
findQuery :: String -> LeanQuery
findQuery name = case [q | q <- queries, queryName q == name] of
    q : _ -> q
    [] -> error ("no query " <> name)

{- | Synthesize one query with a rung, size by size up to the size of the
expected program, and print a result row. The search stops at the expected
program.
-}
runQuery :: String -> String -> Int -> IO ()
runQuery name rung seconds = do
    let q = findQuery name
        bound = programSize (querySolution q)
    directory <- oracleDirectory
    start <- getMonotonicTime
    startNanos <- getMonotonicTimeNSec
    checks <- checksFromEnvironment
    modesText <- lookupEnv "HECTARE_LEAN_MODES"
    modes <- maybe (pure (optionModes defaultOptions)) (either fail pure . readModes) modesText
    withOracle directory [] $ \oracle -> do
        libraryStart <- getMonotonicTimeNSec
        (components, skipped) <- library oracle (rungItems rung)
        libraryEnd <- getMonotonicTimeNSec
        printf "library,%d,%d\n" (length components) (length skipped)
        goal <- enterGoal oracle (querySignature q)
        forM_ (goalErrors goal) $ \message -> printf "error,%s\n" (Text.unpack message)
        configureChecks oracle checks
        firstFit <- newIORef Nothing
        firstTerm <- newIORef ""
        solved <- newIORef Nothing
        let options =
                defaultOptions
                    { optionMaximumSize = bound
                    , optionArgumentOnly = ["id"]
                    , optionAvoid = avoid
                    , optionDeadline = Just (startNanos + fromIntegral seconds * 1000000000)
                    , optionModes = modes
                    , optionReport = Just report
                    }
            report size progress = do
                now <- getMonotonicTime
                printf "size,%d,%s,%.3f\n" size (show progress) (now - start)
                hFlush stdout
            accept fit = do
                known <- readIORef firstFit
                when (isNothing known) $ do
                    writeIORef firstFit (Just fit)
                    writeIORef firstTerm =<< lastTerm oracle
                if fitProgram fit == querySolution q
                    then False <$ writeIORef solved (Just (fitSize fit))
                    else pure True
        -- The walk stops at the deadline between two checks; the time limit
        -- here is for a construction or a reduction that does not stop.
        statistics <- timeout ((seconds + 20) * 1000000) (streamFits oracle options components goal accept)
        end <- getMonotonicTime
        found <- readIORef firstFit
        size <- readIORef solved
        let outcomeText :: String
            outcomeText = case (size, found, statistics) of
                (Just _, _, _) -> "solved"
                (_, _, Nothing) -> "timeout"
                (_, _, Just s) | progressOutOfTime (statisticsProgress s) -> "timeout"
                (_, Just _, _) -> "other"
                _ -> "unsolved"
        -- After a deadline the oracle has answered its last request, so it can
        -- still give its counters.
        figures <- if isNothing statistics then pure Map.empty else counters oracle
        term <- if isNothing size then pure "" else lastTerm oracle
        first <- readIORef firstTerm
        let figure key = Map.findWithDefault 0 key figures
            perExtension :: Integer -> Double
            perExtension nanos = fromIntegral nanos / fromIntegral (max 1 (figure "extensions")) / 1000
            perCount key nanos = fromIntegral (figure nanos) / fromIntegral (max 1 (figure key)) :: Double
            roundTrip =
                maybe
                    0
                    (\s -> fromIntegral (statisticsRoundTripNanos s) / fromIntegral (max 1 (statisticsExtensions s)) / 1000)
                    statistics ::
                    Double
            progress = statisticsProgress <$> statistics
        printf
            "result,%s,%s,%s,%d,%s,%s,%s,%s,%s,%d,%d,%d,%.3f,%d,%.1f,%.1f,%.0f,%.0f,%s,%s,%s\n"
            name
            rung
            outcomeText
            bound
            (maybe "-" (show . fitSize) found)
            (maybe "-" show size)
            (maybe "-" (show . progressPrograms) progress)
            (maybe "-" (show . progressSkipped) progress)
            (maybe "-" (show . statisticsExtensions) statistics)
            (figure "steps")
            (figure "synthCalls")
            (figure "synthPrunes")
            (end - start)
            (oracleImportMilliseconds oracle)
            roundTrip
            (perExtension (figure "extendNanos"))
            (perCount "saves" "saveNanos")
            (perCount "restores" "restoreNanos")
            (maybe "-" (renderProgram . fitProgram) found)
            (Text.unpack first)
            (Text.unpack term)
        hFlush stdout
        printf "counters,%s,%s,%s\n" name rung (show (Map.toList figures))
        forM_ statistics $ \searched -> do
            forM_ (statisticsRuns searched) $ \run ->
                printf
                    "run,%s,%s,%s,%.3f,%d,%d\n"
                    name
                    (Text.unpack (runName run))
                    (show (progressOutcome (runProgress run)))
                    (fromIntegral (runNanos run) / 1e9 :: Double)
                    (progressPrograms (runProgress run))
                    (progressFits (runProgress run))
            forM_ (statisticsStates searched) $ \stateFigures -> printf "figures,%s,%s\n" name (show stateFigures)
        -- The walk times Hectare's construction, reduction, and listing, and
        -- its checks, which hold the round trips.
        let proposed = maybe 0 progressPrograms progress
            mode = modeName (fromMaybe "a" modesText) checks
            row = cascadeRow name rung mode
            part field = maybe 0 (fromIntegral . field) progress :: Double
            hectareNanos = part progressBuildNanos + part progressReduceNanos + part progressListNanos
            roundTripNanos = maybe 0 statisticsRoundTripNanos statistics
            walkOverhead = part progressCheckNanos - fromIntegral roundTripNanos
        row
            "erasure"
            (show (length skipped))
            (show (length components))
            (fromIntegral (libraryEnd - libraryStart) / fromIntegral (max 1 (length components + length skipped)))
            "per constant, once"
        row
            "hectare"
            "-"
            (show proposed)
            (hectareNanos / fromIntegral (max 1 proposed))
            ( printf
                "per program: construction %.0f ms, reduction %.0f ms, listing %.0f ms"
                (part progressBuildNanos / 1e6)
                (part progressReduceNanos / 1e6)
                (part progressListNanos / 1e6)
            )
        row
            "dead-prefix"
            (maybe "-" (show . progressSkipped) progress)
            (maybe "-" (show . statisticsExtensions) statistics)
            (walkOverhead / fromIntegral (max 1 proposed))
            "per program, the checks without the round trips"
        row
            "round-trip"
            "-"
            (show (figure "extensions"))
            (fromIntegral (toInteger roundTripNanos - figure "extendNanos") / fromIntegral (max 1 (figure "extensions")))
            "per program, the pipes and the parsing"
        hostCascade row figure

{- | Search one query with the states that Lean builds from its own goals,
up to the size of the expected program, and print a row with the oracle's
figures.
-}
runStatesQuery :: String -> String -> Int -> IO ()
runStatesQuery name rung seconds = do
    let q = findQuery name
    directory <- oracleDirectory
    start <- getMonotonicTime
    checks <- checksFromEnvironment
    withOracle directory [] $ \oracle -> do
        _ <- library oracle (rungItems rung)
        _ <- enterGoal oracle (querySignature q)
        configureChecks oracle checks
        figures <- searchStates oracle (programSize (querySolution q)) seconds (preorder (querySolution q))
        end <- getMonotonicTime
        let figure key = Text.unpack (Map.findWithDefault "-" key figures)
            outcome :: String
            outcome
                | figure "found" `notElem` ["0", "-"] = "solved"
                | figure "timedOut" == "true" = "timeout"
                | otherwise = "unsolved"
        printf
            "states,%s,%s,%s,%d,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%.3f\n"
            name
            rung
            outcome
            (programSize (querySolution q))
            (figure "programs")
            (figure "fits")
            (figure "relevant")
            (figure "states")
            (figure "transitions")
            (figure "buildSteps")
            (figure "searchSteps")
            (figure "synthCalls")
            (figure "milliseconds")
            (figure "timedOut")
            (end - start)
        let number key = maybe 0 (read . Text.unpack) (Map.lookup key figures) :: Integer
            row = cascadeRow name rung (modeName "b" checks)
        row
            "budget"
            (show (number "budgetPrunes"))
            (show (number "memoLookups"))
            0
            "states with more arguments to use than leaves"
        row
            "memo"
            (show (number "splitPrunes"))
            (show (number "splitPasses"))
            (fromIntegral (number "memoNanos") / fromIntegral (max 1 (number "memoLookups")))
            (printf "per lookup; %d of %d lookups found the state" (number "memoHits") (number "memoLookups"))
        if number "indexLookups" > 0
            then
                row
                    "index"
                    (show (number "indexSkips"))
                    (show (number "indexPasses"))
                    (fromIntegral (number "indexNanos") / fromIntegral (max 1 (number "indexSkips" + number "indexPasses")))
                    ( printf
                        "per leaf and number of children; %d lookups at %.0f ns; %d entries built in %.1f ms"
                        (number "indexLookups")
                        (fromIntegral (number "indexNanos") / fromIntegral (number "indexLookups") :: Double)
                        (number "indexEntries")
                        (fromIntegral (number "indexBuildNanos") / 1000000 :: Double)
                    )
            else row "index" "-" "-" 0 "off"
        hostCascade row number
        hFlush stdout

{- | Read the modes of a portfolio: names separated by commas, each with an
optional budget in seconds after a colon, as @hectare:2,states@.
-}
readModes :: String -> Either String [(Mode, Maybe Double)]
readModes = mapM mode . words . map (\c -> if c == ',' then ' ' else c)
  where
    mode text = case break (== ':') text of
        ("hectare", budget) -> (,) Hectare <$> seconds budget
        ("states", budget) -> (,) States <$> seconds budget
        _ -> Left ("no mode " <> text)
    seconds budget = case budget of
        "" -> Right Nothing
        ':' : number -> maybe (Left ("not seconds: " <> number)) (Right . Just) (readMaybe number)
        _ -> Left ("not a budget: " <> budget)

-- | The optional levels of the oracle's step from @HECTARE_LEAN_CHECKS@.
checksFromEnvironment :: IO [Text]
checksFromEnvironment = maybe [] (filter (not . Text.null) . Text.splitOn "," . Text.pack) <$> lookupEnv "HECTARE_LEAN_CHECKS"

-- | The name of a mode with its optional levels, as @a+head@.
modeName :: String -> [Text] -> String
modeName mode checks = concat (mode : ["+" <> Text.unpack check | check <- checks])

-- | Print a row of the cost cascade.
cascadeRow :: String -> String -> String -> String -> String -> String -> Double -> String -> IO ()
cascadeRow name rung mode level rejections passes nanos note =
    printf "cascade,%s,%s,%s,%s,%s,%s,%.0f,%s\n" name rung mode level rejections passes nanos note

{- | Print the rows of the levels of the oracle's step and complete check,
from its counters.
-}
hostCascade :: (String -> String -> String -> Double -> String -> IO ()) -> (Text -> Integer) -> IO ()
hostCascade row figure = do
    let per nanos decisions = fromIntegral (figure nanos) / fromIntegral (max 1 decisions) :: Double
        steps = figure "steps"
        headChecks = figure "headChecks"
        unifications = steps - figure "arityRejects" - figure "headRejects"
    row
        "arity"
        (show (figure "arityRejects"))
        (show (steps - figure "arityRejects"))
        (per "arityNanos" steps)
        "per step, with the instantiation"
    if headChecks > 0
        then
            row
                "head"
                (show (figure "headRejects"))
                (show (headChecks - figure "headRejects"))
                (per "headNanos" headChecks)
                "per step"
        else row "head" "-" "-" 0 "off"
    row
        "isDefEq"
        (show (figure "unifyRejects"))
        (show (unifications - figure "unifyRejects"))
        (per "unifyNanos" unifications)
        "per step"
    row
        "synthInstance"
        (show (figure "synthPrunes"))
        (show (figure "synthCalls" - figure "synthPrunes"))
        (per "synthNanos" (figure "synthCalls"))
        (printf "per call; %d steps without a call" (figure "synthSkips"))
    row
        "complete"
        (show (figure "completes" - figure "fits"))
        (show (figure "fits"))
        (per "completeNanos" (figure "completes"))
        "per complete program, with Meta.check"
    row
        "snapshot"
        "-"
        (show (figure "saves"))
        (per "saveNanos" (figure "saves"))
        (printf "per saveState; a restore costs %.0f ns" (per "restoreNanos" (figure "restores")))

{- | Search one query with the portfolio: mode (a) for the budget of
@HECTARE_LEAN_BUDGET@ (2 s by default), then, when it did not find the
expected program, the search over states with the index for the rest of the
seconds. The row gives the outcome, the mode that solved the query, the
seconds, and each run's outcome (solved, exhausted, outOfTime, or skipped)
and seconds.
-}
runPortfolioQuery :: String -> String -> Int -> IO ()
runPortfolioQuery name rung seconds = do
    let q = findQuery name
        bound = programSize (querySolution q)
    budget <- maybe 2 read <$> lookupEnv "HECTARE_LEAN_BUDGET" :: IO Double
    directory <- oracleDirectory
    start <- getMonotonicTime
    startNanos <- getMonotonicTimeNSec
    withOracle directory [] $ \oracle -> do
        (components, _) <- library oracle (rungItems rung)
        goal <- enterGoal oracle (querySignature q)
        configureChecks oracle ["index"]
        solved <- newIORef False
        let options =
                defaultOptions
                    { optionMaximumSize = bound
                    , optionArgumentOnly = ["id"]
                    , optionAvoid = avoid
                    , optionDeadline = Just (startNanos + round (budget * 1e9))
                    }
            accept fit
                | fitProgram fit == querySolution q = False <$ writeIORef solved True
                | otherwise = pure True
        statistics <- timeout ((ceiling budget + 20) * 1000000) (streamFits oracle options components goal accept)
        middle <- getMonotonicTime
        solvedA <- readIORef solved
        let hectareOutcome :: String
            hectareOutcome
                | solvedA = "solved"
                | maybe True (progressOutOfTime . statisticsProgress) statistics = "outOfTime"
                | otherwise = "exhausted"
        -- After the time limit here the oracle may be part way through a
        -- request, so the search over states runs only after the walk ended.
        (statesOutcome, end) <-
            if solvedA || isNothing statistics
                then pure ("skipped" :: String, middle)
                else do
                    let remaining = max 1 (floor (fromIntegral seconds - (middle - start)))
                    figures <- searchStates oracle bound remaining (preorder (querySolution q))
                    end <- getMonotonicTime
                    let figure key = Map.findWithDefault "-" key figures
                    pure
                        ( if figure "found" `notElem` ["0", "-"]
                            then "solved"
                            else if figure "timedOut" == "true" then "outOfTime" else "exhausted"
                        , end
                        )
        let outcome, mode :: String
            (outcome, mode)
                | solvedA = ("solved", "a")
                | statesOutcome == "solved" = ("solved", "b")
                | statesOutcome == "outOfTime" || hectareOutcome == "outOfTime" && statesOutcome == "skipped" = ("timeout", "-")
                | otherwise = ("unsolved", "-")
        printf
            "portfolio,%s,%s,%s,%s,%.3f,%s,%.3f,%s,%.3f\n"
            name
            rung
            outcome
            mode
            (end - start)
            hectareOutcome
            (middle - start)
            statesOutcome
            (end - middle)
        hFlush stdout

{- | Run each query in a child process with a time limit, in the mode of the
first argument (@--query@, @--states-query@, or @--portfolio-query@), and
print the rows.
-}
runSuite :: String -> String -> Int -> [String] -> IO ()
runSuite mode rung seconds names = do
    executable <- getExecutablePath
    let (prefix, header) = case mode of
            "--states-query" ->
                ( "states,"
                , "states,query,rung,outcome,bound,programs,fits,relevant,states,transitions,buildSteps,searchSteps,synthCalls,milliseconds,timedOut,seconds"
                )
            "--portfolio-query" ->
                ("portfolio,", "portfolio,query,rung,outcome,mode,seconds,hectare,hectareSeconds,states,statesSeconds")
            _ ->
                ( "result,"
                , "result,query,rung,outcome,bound,first,solved,programs,skipped,extensions,steps,synthCalls,synthPrunes,seconds,importMs,roundTripUs,leanUs,saveNs,restoreNs,firstFit,firstTerm,term"
                )
    putStrLn header
    hFlush stdout
    forM_ (if null names then map queryName queries else names) $ \name -> do
        (code, out, err) <-
            readProcessWithExitCode
                "timeout"
                ["--kill-after=10", show (seconds + 60), executable, mode, name, rung, show seconds, "+RTS", "-M4G", "-RTS"]
                ""
        case [line | line <- lines out, prefix `isPrefixOf` line] of
            line : _ -> do
                putStrLn line
                mapM_ putStrLn [extra | extra <- lines out, any (`isPrefixOf` extra) ["counters,", "cascade,", "run,", "figures,"]]
            [] ->
                putStrLn
                    ( prefix
                        <> name
                        <> ","
                        <> rung
                        <> ","
                        <> (if code == ExitFailure 124 then "timeout" else "crash")
                        <> " "
                        <> show (take 200 err)
                    )
        hFlush stdout

-- | @exact?@ on each query, with every argument required and without.
runSearch :: [String] -> IO ()
runSearch names = do
    directory <- oracleDirectory
    putStrLn "search,query,expected,usingMs,usingTerm,plainMs,plainTerm,warmUsingMs"
    forM_ (if null names then map queryName queries else names) $ \name -> do
        let q = findQuery name
        outcome <- try $ withOracle directory [] $ \oracle -> do
            _ <- enterGoal oracle (querySignature q)
            (usingMs, usingTerm) <- search oracle True
            (plainMs, plainTerm) <- search oracle False
            (warmMs, _) <- search oracle True
            printf
                "search,%s,%s,%d,%s,%d,%s,%d\n"
                name
                (renderProgram (querySolution q))
                usingMs
                (maybe "-" Text.unpack usingTerm)
                plainMs
                (maybe "-" Text.unpack plainTerm)
                warmMs
        case outcome of
            Left e -> printf "search,%s,crash,%s\n" name (show (e :: SomeException))
            Right () -> pure ()
        hFlush stdout

{- | @hectare?@'s search against @exact?@ on each query: the rank of the
expected program among @hectare?@'s fits that use every argument, the fits
before it, the milliseconds, and the first fit; then @exact? using@ with
every argument required, its milliseconds, its term, and whether the term is
the expected program.
-}
runSuggest :: Int -> Int -> [String] -> IO ()
runSuggest seconds budget names = do
    directory <- oracleDirectory
    putStrLn
        "suggest,query,expected,rank,foundBy,fits,milliseconds,hectare,hectareFits,hectareMs,states,statesMs,leaves,first,exactMs,exactTerm,exactExpected"
    forM_ (if null names then map queryName queries else names) $ \name -> do
        let q = findQuery name
        outcome <- try $ withOracle directory [] $ \oracle -> do
            _ <- enterGoal oracle (querySignature q)
            figures <- suggest oracle (programSize (querySolution q)) 1000 seconds True budget (preorder (querySolution q))
            (exactMs, exactTerm) <- search oracle True
            let figure key = Text.unpack (Map.findWithDefault "-" key figures)
                expected = renderProgram (querySolution q)
            printf
                "suggest,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%d,%s,%s\n"
                name
                expected
                (figure "rank")
                (figure "foundBy")
                (figure "fits")
                (figure "milliseconds")
                (figure "hectare")
                (figure "hectareFits")
                (figure "hectareMilliseconds")
                (figure "states")
                (figure "statesMilliseconds")
                (figure "leaves")
                (figure "first")
                exactMs
                (maybe "-" Text.unpack exactTerm)
                (if fmap Text.unpack exactTerm == Just expected then "yes" else "no" :: String)
        case outcome of
            Left e -> printf "suggest,%s,crash,%s\n" name (show (e :: SomeException))
            Right () -> pure ()
        hFlush stdout

{- | The features of each query that predict which mode solves it, read before
the search with the leaves of a rung ("Oracle.Features" on the Lean side).
-}
runFeatures :: String -> [String] -> IO ()
runFeatures rung names = do
    directory <- oracleDirectory
    putStrLn "features,query,rung,higherKinded,classOverConstructor,openChildren,fitting,withoutErasure,milliseconds"
    forM_ (if null names then map queryName queries else names) $ \name -> do
        let q = findQuery name
        outcome <- try $ withOracle directory [] $ \oracle -> do
            _ <- library oracle (rungItems rung)
            _ <- enterGoal oracle (querySignature q)
            figures <- features oracle (programSize (querySolution q))
            let figure key = Text.unpack (Map.findWithDefault "-" key figures)
            printf
                "features,%s,%s,%s,%s,%s,%s,%s,%s\n"
                name
                rung
                (figure "higherKinded")
                (figure "classOverConstructor")
                (figure "openChildren")
                (figure "fitting")
                (figure "withoutErasure")
                (figure "milliseconds")
        case outcome of
            Left e -> printf "features,%s,crash,%s\n" name (show (e :: SomeException))
            Right () -> pure ()
        hFlush stdout

-- | The time of a round trip without work, and of a snapshot pair.
runPing :: Int -> IO ()
runPing count = do
    directory <- oracleDirectory
    withOracle directory [] $ \oracle -> do
        _ <- enterGoal oracle "∀ {α : Type} [BEq α] (x : α) (xs : List α), Nat"
        replicateM_ 1000 (ping oracle)
        start <- getMonotonicTimeNSec
        replicateM_ count (ping oracle)
        end <- getMonotonicTimeNSec
        pair <- snapshots oracle 1000000
        printf
            "ping,%d,%.2f us per round trip,import %d ms,%d ns per saveState and restore\n"
            count
            (fromIntegral (end - start) / fromIntegral count / 1000 :: Double)
            (oracleImportMilliseconds oracle)
            pair
