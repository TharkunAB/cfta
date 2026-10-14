{-# LANGUAGE OverloadedStrings #-}

{- | Mode (b): states built from a host's own goals, without Hectare and
without erasure, and a search over them that the host's checker checks.

A state is a goal (by the host's key: a goal type up to the names of its
unification variables), a size, and the query arguments that the goal's
program must use, as Hectare requires of a whole program: a state with more
such arguments than its size is empty, a leaf that is one of them uses it,
and each of the others goes to one child. A transition of a state is a leaf
with @k@ children whose refinement step passes on the goal, with each split
of the rest of the size and of the arguments over the @k@ children whose
states are not empty.

The host refines a goal ('goalsTransitions'): for the key of a goal and
numbers of children, it gives each leaf whose step passes, with the keys of
the child goals and its place in the host's order. This module does the
rest:

* The table of states, each built on its first visit, and the host's
  refinements by key and number of children, so that the host refines a
  goal once for all sizes. A state that the deadline stops is not kept.
* The transitions of a state in the host's order ('refinementRank'), as
  the leaves whose result head is the goal's first in GHC.
* The search, size by size, in preorder over the table. The state of a
  child is the one that the build recorded, from the child goal before the
  unifications of its siblings. So the table over-approximates the programs
  of a goal, and the host decides: each complete program goes to the
  walk's 'Checker', from the prefix that it shares with the last one, and
  there the unifications of the earlier children reach the later children.
* A prefix that the checker kills goes into the walk's trie of dead
  prefixes. The search leaves the rest of the subtree under it, and it
  skips the same prefix under another split without a call to the host.
* Hectare's rule for the first argument (as for @head []@), and each fit
  once ('hookNew'), as in the walk.

The other way to tie the siblings takes the state of the real goal of each
child, after the unifications of its siblings. It needs the host at each
step of the search, and in GHC it solved the same queries with twice the
states.
-}
module Data.CFTA.Gen.Synthesis.States (
    -- * Hosts
    Budget,
    Goals (..),
    Refinement (..),

    -- * Searches
    Figures (..),
    emptyFigures,
    searchStates,
    budgetSplits,
) where

import Control.Monad (filterM)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.List (delete, sort, sortOn)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)

import Data.CFTA.Gen.Synthesis (Program (..))
import Data.CFTA.Gen.Synthesis.Walk

-- Hosts

-- | The budget of a goal: its size, and the leaves (the query's arguments) that its program must use.
type Budget = (Int, [Int])

-- | The goals of a host: the leaves, the key of the query's goal, and the refinements of a goal.
data Goals m key = Goals
    { goalsLeaves :: [Text]
    -- ^ The names of the leaves, by index: the names in the programs and in the checker's tokens.
    , goalsRequired :: [Int]
    -- ^ The leaves that each program must use: the query's arguments.
    , goalsRoot :: key
    -- ^ The key of the query's goal.
    , goalsTransitions :: Maybe Word64 -> key -> [Int] -> m (Maybe [Refinement key])
    {- ^ The refinements of the goal of a key for numbers of children: each
    leaf whose step passes with one of the numbers of children. 'Nothing'
    when the deadline (a time on the monotonic clock) comes first. No
    unification stays.
    -}
    }

-- | A leaf whose step passes on a goal with a number of children.
data Refinement key = Refinement
    { refinementRank :: !Int
    {- ^ The place of the leaf and its number of children in the host's order
    for the goal. The order does not depend on the numbers of children
    asked, and the search tries the transitions of a state in this order.
    -}
    , refinementLeaf :: !Int
    , refinementChildren :: !Int
    , refinementGoals :: [key]
    -- ^ The keys of the child goals.
    }

-- Searches

-- | The figures of a search over states, next to the walk's 'Progress'.
data Figures = Figures
    { figuresStates :: !Int
    -- ^ The states built.
    , figuresEmpty :: !Int
    -- ^ The states without a transition.
    , figuresTransitions :: !Int
    -- ^ The transitions of the states built.
    , figuresRefinements :: !Int
    -- ^ The calls of 'goalsTransitions'.
    , figuresSplits :: !Int
    -- ^ The splits whose children's states are not empty.
    , figuresSplitsBound :: !Int
    -- ^ The splits that the argument bound left out.
    , figuresSplitsEmpty :: !Int
    -- ^ The splits that the empty state of a child left out.
    , figuresSearchSteps :: !Int
    -- ^ The transitions that the search took.
    }
    deriving (Eq, Show)

-- | The figures before the first state.
emptyFigures :: Figures
emptyFigures = Figures 0 0 0 0 0 0 0 0

{- | A transition: a leaf, its number of children, and the splits of the rest
of the budget, each child with its budget and the key of its goal.
-}
data Transition key = Transition
    { transitionLeaf :: !Int
    , transitionChildren :: !Int
    , transitionSplits :: [[(Budget, key)]]
    }

-- | The state of a search.
data Search key = Search
    { searchRefined :: Map key (IntMap [Refinement key])
    -- ^ The host's refinements, for each key and number of children.
    , searchTable :: Map (key, Budget) [Transition key]
    -- ^ The transitions of each state built.
    , searchHeld :: [Token]
    -- ^ The tokens of the host's frames.
    , searchDead :: Dead
    , searchProgress :: !Progress
    , searchFigures :: !Figures
    }

-- | How a part of the search ended.
data Result
    = -- | Go on with the next program.
      Continue
    | -- | The token at this index, counted from the root, failed.
      DiedAt !Int
    | -- | Stop the search.
      Halt !Outcome

{- | Search the programs of the host's goals over states, size by size, with
the host's checker, and call the function on each new fit ('hookNew'); stop
when it returns 'False', at a limit, or after the last size. The rules are
Hectare's pruning rules, with the names of the leaves: a leaf of the first
list does not get a leaf of the second list (with 'Nothing': any leaf) as
its first argument.

The 'Progress' has the time of the builds of the states
('progressBuildNanos'), of the search itself ('progressListNanos'), and of
the checks. 'progressPrograms' counts the complete programs that the search
gave to the host, and 'progressSkipped' the prefixes under a dead prefix.
As in the walk, the host holds no frame before the function gets a fit, and
none at the end. It also holds none while it refines the goals of a size.
-}
searchStates ::
    (MonadIO m, Ord key) =>
    Limits ->
    Checker m ->
    Hooks m ->
    Goals m key ->
    [([Text], Maybe [Text])] ->
    (Fit -> m Bool) ->
    m (Progress, Figures)
searchStates limits checker hooks goals avoid accept = do
    begin <- liftIO getMonotonicTimeNSec
    reference <- liftIO (newIORef (Search Map.empty Map.empty [] emptyDead emptyProgress emptyFigures))
    let current = liftIO (readIORef reference)
        change f = liftIO (modifyIORef' reference f)
        progress f = change (\s -> s{searchProgress = f (searchProgress s)})
        figures f = change (\s -> s{searchFigures = f (searchFigures s)})
        deadline = limitDeadline limits
        late = maybe (pure False) (\end -> (>= end) <$> liftIO getMonotonicTimeNSec) deadline
        outOfTime = progress (\p -> p{progressOutOfTime = True})
        timedOut = progressOutOfTime . searchProgress <$> current
        names = IntMap.fromList (zip [0 ..] (goalsLeaves goals))
        name leaf = IntMap.findWithDefault "" leaf names
        -- The host's refinements of a key for the numbers of children, in
        -- the host's order. The host refines only the numbers that it did
        -- not refine before.
        refinements key counts = do
            known <- Map.findWithDefault IntMap.empty key . searchRefined <$> current
            let missing = filter (`IntMap.notMember` known) counts
            refined <-
                if null missing
                    then pure (Just known)
                    else do
                        stop <- (||) <$> timedOut <*> late
                        if stop
                            then Nothing <$ outOfTime
                            else do
                                figures (\f -> f{figuresRefinements = figuresRefinements f + 1})
                                answer <- goalsTransitions goals deadline key missing
                                case answer of
                                    Nothing -> Nothing <$ outOfTime
                                    Just found -> do
                                        let known' =
                                                IntMap.union known . IntMap.fromListWith (flip (<>)) $
                                                    [(k, []) | k <- missing] <> [(refinementChildren r, [r]) | r <- found]
                                        change (\s -> s{searchRefined = Map.insert key known' (searchRefined s)})
                                        pure (Just known')
            pure (sortOn refinementRank [r | Just table <- [refined], k <- counts, r <- IntMap.findWithDefault [] k table])
        -- The transitions of a state, built on the first visit.
        stateOf key budget@(size, arguments) = do
            known <- Map.lookup (key, budget) . searchTable <$> current
            case known of
                Just transitions -> pure transitions
                Nothing
                    | length arguments > size -> remember key budget []
                    | otherwise -> do
                        refined <- refinements key (childCounts size)
                        transitions <- concat <$> mapM (transition size arguments) refined
                        stop <- timedOut
                        if stop then pure transitions else remember key budget transitions
        -- The transition of a refinement, with the splits whose children's
        -- states are not empty.
        transition size arguments (Refinement _ leaf k children) = do
            let (splits, bounded) = budgetSplits (size - 1) (delete leaf arguments) k
            kept <- filterM (\split -> inhabited (zip split children)) splits
            figures $ \f ->
                f
                    { figuresSplits = figuresSplits f + length kept
                    , figuresSplitsBound = figuresSplitsBound f + bounded
                    , figuresSplitsEmpty = figuresSplitsEmpty f + length splits - length kept
                    }
            pure [Transition leaf k [zip split children | split <- kept] | not (null kept)]
        -- Whether the states of the children are not empty; the first empty one stops the builds.
        inhabited children = case children of
            [] -> pure True
            (budget, key) : rest -> do
                transitions <- stateOf key budget
                if null transitions then pure False else inhabited rest
        remember key budget transitions = do
            change (\s -> s{searchTable = Map.insert (key, budget) transitions (searchTable s)})
            figures $ \f ->
                f
                    { figuresStates = figuresStates f + 1
                    , figuresEmpty = figuresEmpty f + fromEnum (null transitions)
                    , figuresTransitions = figuresTransitions f + length transitions
                    }
            pure transitions
        -- Search the programs of the goals on the stack, each with its budget
        -- and key, after the tokens so far (innermost first). The previous
        -- token is the parent of the first goal when it has children.
        search stack tokens previous = case stack of
            [] -> check (reverse tokens)
            (budget, key) : rest -> do
                stop <- late
                if stop
                    then Halt OutOfTime <$ outOfTime
                    else do
                        transitions <- stateOf key budget
                        let position = length tokens
                            go [] = pure Continue
                            go (next : more)
                                | avoided previous next = go more
                                | otherwise = do
                                    let token = (name (transitionLeaf next), transitionChildren next)
                                    dead <- isDead (reverse (token : tokens)) . searchDead <$> current
                                    if dead
                                        then progress (\p -> p{progressSkipped = progressSkipped p + 1}) >> go more
                                        else do
                                            figures (\f -> f{figuresSearchSteps = figuresSearchSteps f + 1})
                                            result <- splits token (transitionSplits next)
                                            case result of
                                                Continue -> go more
                                                _ -> pure result
                            -- The splits of a transition. A death of its own
                            -- token ends them, and one further down ends one split.
                            splits _ [] = pure Continue
                            splits token (split : others) = do
                                result <- search (split <> rest) (token : tokens) (Just token)
                                case result of
                                    Continue -> splits token others
                                    DiedAt index
                                        | index == position -> pure Continue
                                        | index > position -> splits token others
                                    _ -> pure result
                        go transitions
        -- In preorder, a goal right after a leaf with children is its first child.
        avoided previous next = case previous of
            Just (parent, arity)
                | arity >= 1 && transitionChildren next == 0 ->
                    or
                        [ parent `elem` heads && maybe True (name (transitionLeaf next) `elem`) arguments
                        | (heads, arguments) <- avoid
                        ]
            _ -> False
        -- Check a complete program, from the prefix that the host holds.
        check tokens = do
            s <- current
            if maybe False (progressPrograms (searchProgress s) >=) (limitPrograms limits)
                then pure (Halt Exhausted)
                else do
                    let program = fromPreorder tokens
                        size = length tokens
                    hookProgram hooks size program
                    before <- liftIO getMonotonicTimeNSec
                    if maybe False (before >=) deadline
                        then Halt OutOfTime <$ outOfTime
                        else do
                            let kept = commonPrefix (searchHeld s) tokens
                            checkerTruncate checker kept
                            extension <- checkerExtend checker (drop kept tokens)
                            after <- liftIO getMonotonicTimeNSec
                            progress $ \p ->
                                p{progressPrograms = progressPrograms p + 1, progressCheckNanos = progressCheckNanos p + (after - before)}
                            case extension of
                                Died index -> do
                                    change $ \s' ->
                                        s'{searchHeld = take index tokens, searchDead = markDead (take (index + 1) tokens) (searchDead s')}
                                    pure (DiedAt index)
                                Done True -> do
                                    new <- hookNew hooks tokens
                                    if new
                                        then do
                                            -- The function gets the host from the start.
                                            checkerTruncate checker 0
                                            change (\s' -> s'{searchHeld = []})
                                            progress (\p -> p{progressFits = progressFits p + 1})
                                            more <- accept (Fit program size)
                                            pure (if more then Continue else Halt Solved)
                                        else Continue <$ change (\s' -> s'{searchHeld = tokens})
                                Done False -> Continue <$ change (\s' -> s'{searchHeld = tokens})
        -- Build the states of each size from the root, then search them.
        sizes size
            | size > limitSize limits = finish Exhausted
            | otherwise = do
                progress (\p -> p{progressSize = size})
                let root = goalsRoot goals
                    budget = (size, sort (goalsRequired goals))
                -- The host refines goals with no frame held.
                checkerTruncate checker 0
                change (\s -> s{searchHeld = []})
                before <- liftIO getMonotonicTimeNSec
                _ <- stateOf root budget
                after <- liftIO getMonotonicTimeNSec
                progress (\p -> p{progressBuildNanos = progressBuildNanos p + (after - before)})
                stop <- timedOut
                if stop
                    then halt OutOfTime
                    else do
                        result <- search [(budget, root)] [] Nothing
                        case result of
                            Halt outcome -> halt outcome
                            _ -> do
                                hookSize hooks size . searchProgress =<< current
                                sizes (size + 1)
        halt outcome = do
            p <- searchProgress <$> current
            hookSize hooks (progressSize p) p
            finish outcome
        -- Leave the host as it was before the search.
        finish outcome = do
            checkerTruncate checker 0
            end <- liftIO getMonotonicTimeNSec
            s <- current
            let p = searchProgress s
                parts = progressBuildNanos p + progressCheckNanos p
                total = end - begin
            pure (p{progressOutcome = outcome, progressListNanos = if total > parts then total - parts else 0}, searchFigures s)
    sizes 1
  where
    childCounts size = if size == 1 then [0] else [1 .. size - 1]
    commonPrefix (x : xs) (y : ys) | x == y = 1 + commonPrefix xs ys
    commonPrefix _ _ = 0 :: Int

{- | The splits of a size and of the arguments to use over @k@ children: the
sizes (each at least one), and for each child the arguments that it uses,
with no child that must use more arguments than its size. The second element
counts the splits that this bound left out.
-}
budgetSplits :: Int -> [Int] -> Int -> ([[Budget]], Int)
budgetSplits size arguments k = (kept, length every - length kept)
  where
    every = [zip sizes sets | sizes <- compositions size k, sets <- assignments arguments k]
    kept = filter (all (\(childSize, set) -> length set <= childSize)) every
    compositions total parts
        | parts == 0 = [[] | total == 0]
        | otherwise = [first : others | first <- [1 .. total - parts + 1], others <- compositions (total - first) (parts - 1)]
    assignments [] parts = [replicate parts []]
    assignments (argument : rest) parts =
        [ [if child == chosen then sort (argument : set) else set | (child, set) <- zip [0 ..] sets]
        | sets <- assignments rest parts
        , chosen <- [0 .. parts - 1 :: Int]
        ]

-- | A program from its tokens in preorder.
fromPreorder :: [Token] -> Program
fromPreorder = fst . tree
  where
    tree tokens = case tokens of
        (leaf, children) : rest ->
            let (arguments, rest') = trees children rest
             in (foldl App (Var leaf) arguments, rest')
        [] -> (Var "", [])
    trees :: Int -> [Token] -> ([Program], [Token])
    trees 0 rest = ([], rest)
    trees n rest =
        let (first, rest') = tree rest
            (others, rest'') = trees (n - 1) rest'
         in (first : others, rest'')
