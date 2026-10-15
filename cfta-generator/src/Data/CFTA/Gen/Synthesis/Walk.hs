{-# LANGUAGE OverloadedStrings #-}

{- | Hectare proposes, a host checks: the part of a checked synthesis that does
not depend on the host.

A host is a typechecker with real types, as GHC's. It erases the types of its
leaves (the components and the arguments of a query) to Hectare's
first-order types, and it checks a program in preorder, one leaf at a time:
each step gives the leftmost open goal a leaf with so many children. This
module does the rest:

* Hectare's automaton of each size over the erased leaves: its construction,
  its reduction, and the listing of its programs, smallest size first, in
  Hectare's enumeration order, each program of representatives once, with
  each group representative expanded. Each part has its own time, and a
  deadline stops the construction or the reduction.
* Each program in preorder ('preorder'), checked by the host from the longest
  prefix that it shares with the host's frames. A prefix that fails goes into
  a trie of dead prefixes, and every later program under it is skipped
  without a call to the host.
* The fits, each program once: a program that fits again (as from two erased
  types of one leaf) is not a new fit.

The host gives a 'Checker'. It keeps a stack of frames, one for each checked
token of the current prefix: frame @i@ holds the host's snapshot from before
step @i@, and its state after it. 'checkerTruncate' keeps the first frames,
and 'checkerExtend' steps more tokens and checks the complete program. A
whole program is one call, so that a host can keep its own per-step state
(as a table of verdicts) and a host in another process can answer a program
in one round trip.

A leaf's name in Hectare is its name in the programs, optionally followed by
a space and a tag, when one leaf has several erased types (as a
higher-kinded component at each type head of a query). The walk drops the
tag from the programs.
-}
module Data.CFTA.Gen.Synthesis.Walk (
    -- * Leaves
    Role (..),
    Erased (..),

    -- * Programs in preorder
    Token,
    preorder,

    -- * Checkers
    Checker (..),
    Extension (..),

    -- * Walks
    Limits (..),
    Hooks (..),
    Fit (..),
    Progress (..),
    emptyProgress,
    walk,
) where

import Control.Exception (evaluate)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)
import System.Timeout (timeout)

import Data.CFTA.Gen.Synthesis (
    Program (..),
    Query (..),
    Type,
    expand,
    library,
    programRuns,
    rawSearchSpace,
    reduceFully,
 )
import Data.CFTA.Interned (refold)

-- Leaves

-- | How Hectare may use a leaf.
data Role
    = -- | A component: an argument of an application, or its head.
      Component
    | -- | A component that only appears as an argument, as @id@.
      ArgumentOnly
    | -- | An argument of the query, which every program must use.
      Required
    deriving (Eq, Show)

{- | A leaf with its name in Hectare (its name in the programs, optionally
with a space and a tag), its erased type, and its role.
-}
data Erased = Erased
    { erasedName :: Text
    , erasedType :: Type
    , erasedRole :: Role
    }
    deriving (Eq, Show)

-- Programs in preorder

-- | A leaf of a program in preorder: its name and its number of children.
type Token = (Text, Int)

-- | A program in preorder: each head leaf with its number of children.
preorder :: Program -> [Token]
preorder program = (name, length arguments) : concatMap preorder arguments
  where
    (name, arguments) = spine program
    spine (Var leaf) = (leaf, [])
    spine (App function argument) = let (leaf, rest) = spine function in (leaf, rest <> [argument])

-- Checkers

{- | A host's checker of programs in preorder. It keeps a stack of frames, one
for each checked token of the current prefix: frame @i@ holds the host's
snapshot from before step @i@, and its state after it.
-}
data Checker m = Checker
    { checkerTruncate :: Int -> m ()
    {- ^ Keep this many frames: restore the snapshot of the first frame that
    goes, if any.
    -}
    , checkerExtend :: [Token] -> m Extension
    {- ^ Step the tokens after the current prefix, one frame each, then check
    the complete program.
    -}
    }

-- | The outcome of an extension.
data Extension
    = {- | The token at this index, counted from the root, failed. The host
      holds the frames before that token, as before the failed step.
      -}
      Died !Int
    | -- | Every token stepped; whether the complete program fits.
      Done !Bool
    deriving (Eq, Show)

-- Walks

-- | The limits of a walk.
data Limits = Limits
    { limitSize :: Int
    -- ^ The largest program, in leaves.
    , limitPrograms :: Maybe Int
    -- ^ The number of Hectare's programs to stop after.
    , limitDeadline :: Maybe Word64
    -- ^ The time on the monotonic clock, in nanoseconds, to stop at.
    }

-- | Functions that a walk calls.
data Hooks m = Hooks
    { hookSize :: Int -> Progress -> m ()
    -- ^ After the programs of each size, and when the walk stops.
    , hookProgram :: Int -> Program -> m ()
    -- ^ Before each program is checked, with its size.
    }

-- | A program that fits, with its size in leaves.
data Fit = Fit
    { fitProgram :: Program
    , fitSize :: Int
    }
    deriving (Eq, Show)

-- | The figures of a walk.
data Progress = Progress
    { progressPrograms :: !Int
    -- ^ The programs that Hectare proposed.
    , progressRuns :: !Int
    {- ^ The typed terms that Hectare listed. One program can have several
    typed terms, and Hectare proposes it once.
    -}
    , progressSkipped :: !Int
    -- ^ The programs under a dead prefix, skipped without a call to the host.
    , progressFits :: !Int
    , progressSize :: !Int
    -- ^ The size of the last program looked at.
    , progressOutOfTime :: !Bool
    -- ^ Whether the walk stopped at the deadline.
    , progressBuildNanos :: !Word64
    -- ^ The time of Hectare's construction of the automata.
    , progressReduceNanos :: !Word64
    -- ^ The time of Hectare's reduction of the automata.
    , progressListNanos :: !Word64
    -- ^ The time to list Hectare's programs.
    , progressCheckNanos :: !Word64
    -- ^ The time of the host's checks.
    }
    deriving (Eq, Show)

-- | The figures before the first program.
emptyProgress :: Progress
emptyProgress = Progress 0 0 0 0 0 False 0 0 0 0

{- | The state of a walk: the tokens of the host's frames, the dead prefixes,
the fits so far, and the figures.
-}
data State = State
    { stateHeld :: [Token]
    , stateDead :: Dead
    , stateReported :: Set [Token]
    , stateProgress :: !Progress
    }

{- | Check Hectare's programs over the erased leaves for an erased goal type,
size by size, with the host's checker, and call the function on each new fit;
stop when it returns 'False', at a limit, or after the last size. The rules
of the second argument are Hectare's pruning rules for programs of size two,
with the leaves' names in Hectare: a leaf of the first list is not applied to
one of the second list (with 'Nothing': to any).

Before the function gets a fit, the host holds no frame, so that the function
can use the host from the start. At the end the host holds no frame, so it is
as it was before the walk.
-}
walk ::
    (MonadIO m) =>
    Limits ->
    Checker m ->
    Hooks m ->
    [Erased] ->
    [([Text], Maybe [Text])] ->
    Type ->
    (Fit -> m Bool) ->
    m Progress
walk limits checker hooks leaves avoid goal accept = sizes 1 (State [] emptyDead Set.empty emptyProgress)
  where
    -- Hectare's automaton has symbols of its own, as app and filter, so each
    -- name gets a prefix there.
    prefix = ("leaf:" <>)
    unprefix program = case program of
        Var name -> Var (Text.takeWhile (/= ' ') (fromMaybe name (Text.stripPrefix "leaf:" name)))
        App function argument -> App (unprefix function) (unprefix argument)
    named role = [(prefix (erasedName leaf), erasedType leaf) | leaf <- leaves, erasedRole leaf == role]
    hectareLibrary =
        library
            (named Component)
            (named ArgumentOnly)
            [(map prefix heads, map prefix <$> arguments) | (heads, arguments) <- avoid]
    hectareQuery = Query (named Required) goal
    deadline = limitDeadline limits
    progressOf = stateProgress
    withProgress state change = state{stateProgress = change (stateProgress state)}
    -- Build and reduce the automaton of each size, then check its programs,
    -- so that each part has its own time.
    sizes size state
        | size > limitSize limits = finish state
        | otherwise = do
            (built, buildTime) <- liftIO (timed deadline (rawSearchSpace hectareLibrary hectareQuery size))
            let state' = withProgress state $ \p -> p{progressSize = size, progressBuildNanos = progressBuildNanos p + buildTime}
            case built of
                Nothing -> stop (withProgress state' $ \p -> p{progressOutOfTime = True})
                Just raw -> do
                    (reduced, reduceTime) <- liftIO (timed deadline (refold (reduceFully raw)))
                    let state'' = withProgress state' $ \p -> p{progressReduceNanos = progressReduceNanos p + reduceTime}
                    case reduced of
                        Nothing -> stop (withProgress state'' $ \p -> p{progressOutOfTime = True})
                        Just space ->
                            -- Each run is a Nothing, then the programs of its
                            -- representatives if they are new.
                            programs
                                size
                                [ program
                                | run <- programRuns space
                                , program <- Nothing : maybe [] (map Just . expand hectareLibrary) run
                                ]
                                state''
    programs size remaining state
        | maybe False (progressPrograms (progressOf state) >=) (limitPrograms limits) = stop state
        | otherwise = do
            (next, listTime) <- liftIO (timed Nothing (nextProgram 0 remaining))
            let listed = maybe 0 fst next
                state' = withProgress state $ \p -> p{progressRuns = progressRuns p + listed, progressListNanos = progressListNanos p + listTime}
            case snd <$> next of
                Just (Just (program, tokens, rest)) -> do
                    hookProgram hooks size program
                    before <- liftIO getMonotonicTimeNSec
                    if maybe False (before >=) deadline
                        then stop (withProgress state' $ \p -> p{progressOutOfTime = True})
                        else do
                            (checked, fit) <-
                                check (withProgress state' $ \p -> p{progressPrograms = progressPrograms p + 1}) size program tokens
                            after <- liftIO getMonotonicTimeNSec
                            let state'' = withProgress checked $ \p -> p{progressCheckNanos = progressCheckNanos p + (after - before)}
                            more <- maybe (pure True) accept fit
                            if more then programs size rest state'' else stop state''
                _ -> hookSize hooks size (progressOf state') >> sizes (size + 1) state'
    -- The next program, with its tokens evaluated, so that the listing has
    -- its own time, and the number of runs before it.
    nextProgram :: Int -> [Maybe Program] -> (Int, Maybe (Program, [Token], [Maybe Program]))
    nextProgram listed remaining = case remaining of
        [] -> listed `seq` (listed, Nothing)
        Nothing : rest -> nextProgram (listed + 1) rest
        Just representative : rest ->
            let program = unprefix representative
                tokens = preorder program
             in listed `seq` forceTokens tokens `seq` (listed, Just (program, tokens, rest))
    forceTokens = foldr (\(name, children) rest -> name `seq` children `seq` rest) ()
    stop state = hookSize hooks (progressSize (progressOf state)) (progressOf state) >> finish state
    -- Leave the host as it was before the walk.
    finish state = progressOf state <$ checkerTruncate checker 0
    check state size program tokens
        | isDead tokens (stateDead state) =
            pure (withProgress state (\p -> p{progressSkipped = progressSkipped p + 1, progressSize = size}), Nothing)
        | otherwise = do
            let kept = commonPrefix (stateHeld state) tokens
                sized = withProgress state $ \p -> p{progressSize = size}
            checkerTruncate checker kept
            extension <- checkerExtend checker (drop kept tokens)
            case extension of
                Died index ->
                    pure (sized{stateHeld = take index tokens, stateDead = markDead (take (index + 1) tokens) (stateDead state)}, Nothing)
                Done True
                    | Set.notMember tokens (stateReported state) -> do
                        -- A new fit: the function gets the host from the start,
                        -- and the next program starts from the root.
                        checkerTruncate checker 0
                        pure
                            ( withProgress
                                sized{stateHeld = [], stateReported = Set.insert tokens (stateReported state)}
                                (\p -> p{progressFits = progressFits p + 1})
                            , Just (Fit program size)
                            )
                _ -> pure (sized{stateHeld = tokens}, Nothing)
    commonPrefix (x : xs) (y : ys) | x == y = 1 + commonPrefix xs ys
    commonPrefix _ _ = 0 :: Int

{- | Evaluate a value to weak head normal form, and give the nanoseconds that
it took; the value is 'Nothing' when the deadline comes first. Only a pure
value is stopped: a host's step that stops part way would leave its state
changed.
-}
timed :: Maybe Word64 -> a -> IO (Maybe a, Word64)
timed deadline value = do
    begin <- getMonotonicTimeNSec
    result <- case deadline of
        Nothing -> Just <$> evaluate value
        Just end
            | begin >= end -> pure Nothing
            | otherwise -> timeout (fromIntegral ((end - begin) `div` 1000)) (evaluate value)
    end' <- getMonotonicTimeNSec
    pure (result, end' - begin)

-- | A trie of dead prefixes: whether the prefix so far is dead, and the longer prefixes.
data Dead = Dead !Bool !(Map Token Dead)

-- | No dead prefix.
emptyDead :: Dead
emptyDead = Dead False Map.empty

-- | Whether a prefix of the tokens is dead.
isDead :: [Token] -> Dead -> Bool
isDead tokens (Dead dead next)
    | dead = True
    | otherwise = case tokens of
        [] -> False
        token : rest -> maybe False (isDead rest) (Map.lookup token next)

-- | Mark a prefix dead.
markDead :: [Token] -> Dead -> Dead
markDead tokens (Dead dead next) = case tokens of
    [] -> Dead True Map.empty
    token : rest -> Dead dead (Map.insert token (markDead rest (Map.findWithDefault emptyDead token next)) next)
