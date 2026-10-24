{-# LANGUAGE DeriveFunctor #-}

{- | Trace languages: the step sequences that a state machine accepts, as the
terms of a finite tree automaton.

A 'StateMachine' has an initial state, a list of steps, the next state of a
step in a state, and the final states, in which a trace can end. A step can
run in a state when it has a next state there: this is the precondition of
the step. A trace of the steps @s1 ... sn@ is the
right spine @Step s1 (Step s2 (... (Step sn End)))@, so the preorder of the
term is the trace, and a prefix of a trace is a preorder prefix of its term.
A trace of @n@ steps has size @n + 1@.

'traceAutomaton' makes the automaton of the traces. Its states are the states
that the initial state reaches, so the state space must be finite. The
automaton has at most one transition for each state and symbol, so each trace
has one run. Thus the automaton is unambiguous, and "Data.CFTA.Sized" and the
generators of @cfta-generator@ count, rank, unrank, sample, and shrink its
traces exactly. Operations on automata apply to it: 'Data.CFTA.intersect'
gives the traces of two state machines over one step type, and
'Data.CFTA.Lowering.lift' gives the traces whose lowering is a trace.

'feasibility' runs a sequence of steps from the root of an automaton. It
gives the shortest prefix that has no run, and the states in which its last
symbol fails.

An automaton can have more than one run of a trace, for example after
'Data.CFTA.mapSymbols' maps two steps to one. Then "Data.CFTA.Sized" lists
each class to count it, and the generators can reject it. 'determinize' makes the
automaton with one run for each trace. 'concatenate', 'project', and
'projectMaybe' use it, so their results are deterministic too.
-}
module Data.CFTA.Trace (
    TraceSymbol (..),
    StateMachine (..),
    traceAutomaton,
    traceTerm,
    traceSteps,
    Infeasible (..),
    feasibility,
    determinize,
    concatenate,
    project,
    projectMaybe,
) where

import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)

import Data.CFTA (FTA, PlainFTA, Transition (..))
import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (noConstraint)
import Data.CFTA.Internal.Tree (explore)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | A node of a trace term: a step with the rest of the trace as its child, or the end of the trace.
data TraceSymbol step
    = Step !step
    | End
    deriving (Eq, Ord, Show, Functor, Generic)

instance (Hashable step) => Hashable (TraceSymbol step)

-- | A state machine over an abstract state: the precondition and the next state of each step, and the final states.
data StateMachine state step = StateMachine
    { machineInitial :: state
    -- ^ The state before the first step.
    , machineSteps :: [step]
    -- ^ The steps.
    , machineNext :: state -> step -> Maybe state
    {- ^ The state after a step. 'Nothing' when the precondition of the step
    is false in the state.
    -}
    , machineFinal :: state -> Bool
    -- ^ Whether a trace can end in the state.
    }

{- | The automaton of the traces of a state machine. Each state that the initial
state reaches is a state of the automaton. A state has an 'End' leaf when it
is final, and a 'Step' transition to the next state for each step whose
precondition is true in it. A state from which no final state is reachable
keeps its row, so 'feasibility' finds the step whose precondition is false.
'FTA.trim' removes these states.
-}
traceAutomaton :: (Ord state, Ord step) => StateMachine state step -> PlainFTA state (TraceSymbol step)
traceAutomaton StateMachine{machineInitial, machineSteps, machineNext, machineFinal} =
    -- Each child is a reached state, and each symbol has one arity, so validation cannot fail.
    fromRight (error "traceAutomaton: the automaton of a state machine is valid")
        $ FTA.mkFTA machineInitial
        $ explore row FTA.transitionChildren machineInitial
  where
    row state =
        [Transition End [] noConstraint | machineFinal state]
            <> [ Transition (Step step) [next] noConstraint
               | step <- machineSteps
               , Just next <- [machineNext state step]
               ]

-- | The term of a sequence of steps.
traceTerm :: [step] -> Term (TraceSymbol step)
traceTerm = foldr (\step rest -> Term.Node (Step step) [rest]) (Term.Node End [])

-- | The steps of a trace term. 'Nothing' when the term is not a right spine that ends in 'End'.
traceSteps :: Term (TraceSymbol step) -> Maybe [step]
traceSteps (Term.Node End []) = Just []
traceSteps (Term.Node (Step step) [rest]) = (step :) <$> traceSteps rest
traceSteps _ = Nothing

{- | Why a sequence of steps is not a trace. 'infeasibleSteps' followed by
'infeasibleSymbol' is the shortest prefix of the sequence that has no run:
each step of 'infeasibleSteps' has a transition, and the symbol has none.
After 'FTA.trim', it is also the shortest prefix that no trace starts with.
-}
data Infeasible state step = Infeasible
    { infeasibleSteps :: ![step]
    -- ^ The steps that run.
    , infeasibleSymbol :: !(TraceSymbol step)
    {- ^ The symbol that has no transition after them: a step whose
    precondition is false, or 'End' when no state is final.
    -}
    , infeasibleStates :: ![state]
    -- ^ The states after 'infeasibleSteps'. The symbol has no transition in each of them.
    }
    deriving (Eq, Show)

{- | Run a sequence of steps from the initial state of an automaton of
traces: the final states after the sequence, or the shortest prefix that
has no run. Each step goes from each current state to each child of
its transitions, so the result is correct for an automaton with more than one
run of a trace, such as an image under 'FTA.mapSymbols'. For an automaton
from 'traceAutomaton', or an intersection of them, there is one state at each
step. The function does not interpret transition annotations.

'FTA.acceptsM' gives only whether the automaton accepts the term, and it
checks a transition after the children of the transition: for a trace term,
from the last step to the first. This function reads the first step first,
so it stops at the first failure.
-}
feasibility ::
    (Ord state, Eq step) =>
    FTA state (TraceSymbol step) annotation -> [step] -> Either (Infeasible state step) [state]
feasibility automaton = go [] [FTA.initialState automaton]
  where
    go done states [] = case [state | state <- states, not $ null $ successors End state] of
        [] -> Left $ Infeasible (reverse done) End states
        final -> Right final
    go done states (step : rest) = case nubOrd $ concat $ concatMap (successors $ Step step) states of
        [] -> Left $ Infeasible (reverse done) (Step step) states
        next -> go (step : done) next rest
    -- The children of each transition with the symbol.
    successors symbol state =
        [ transitionChildren transition
        | transition <- FTA.transitionsFrom automaton state
        , transitionSymbol transition == symbol
        ]

{- | The deterministic automaton of the traces that an automaton accepts: the
subset construction. A state of the result is the set of the states in which
the input can be after a prefix of a trace. It has an 'End' leaf when one of
its states has one. For each step, it has one 'Step' transition to the set
of the children of the transitions with that step. So each state has at most
one transition for each symbol, and each trace has one run. Thus
"Data.CFTA.Sized" counts and ranks the traces with its count table, and the
generators accept the result.

The construction builds only the sets that the initial set reaches, and not
the empty set. For an input of @n@ states and @k@ steps, the result has at
most @2^n - 1@ states, one for each non-empty set of input states, and each
state has at most @k + 1@ transitions. Some inputs reach the bound on the
states: the traces whose @m@-th step from the end is a given step have an
automaton of @m + 1@ states, and its result has @2^m@ states. An input with
one run for each prefix, such as an automaton from 'traceAutomaton', gives a
result of at most @n@ states.

The function reads only the transitions of trace terms: 'End' with no child
and 'Step' with one child. It does not interpret annotations.
-}
determinize ::
    (Ord state, Ord step) =>
    FTA state (TraceSymbol step) annotation -> PlainFTA (Set state) (TraceSymbol step)
determinize automaton = subsets (edges automaton) (const []) (FTA.initialState automaton)

{- | The traces that are a trace of the first automaton followed by a trace of
the second. A trace can continue with a trace of the second automaton where
a trace of the first can end. A trace that splits in more than one way has
one run, because the result comes from the subset construction of
'determinize'. For inputs of @n@ and @m@ states, the result has at most
@2^(n + m) - 1@ states, and at most @(n + 1) * 2^m@ states when the first
input has one run for each prefix, as an automaton from 'traceAutomaton'
has. The function does not interpret annotations.
-}
concatenate ::
    (Ord left, Ord right, Ord step) =>
    FTA left (TraceSymbol step) leftAnnotation ->
    FTA right (TraceSymbol step) rightAnnotation ->
    PlainFTA (Set (Either left right)) (TraceSymbol step)
concatenate before after = subsets edgesOf continue (Left $ FTA.initialState before)
  where
    edgesOf (Left state) = [(symbol, map Left children) | (symbol, children) <- edges before state, symbol /= End]
    edgesOf (Right state) = [(symbol, map Right children) | (symbol, children) <- edges after state]
    -- Where a trace of the first automaton can end, the second automaton starts without a step.
    continue (Left state) = [Right $ FTA.initialState after | (End, []) `elem` edges before state]
    continue (Right _) = []

{- | The traces of an automaton with each step replaced by its image: a
projection to a coarser alphabet of steps. Two steps with one image can give
two runs of one trace, as in 'FTA.mapSymbols'. The result comes from the
subset construction of 'determinize', so it has one run for each trace, and
the same bound on its size. The function does not interpret annotations.
-}
project ::
    (Ord state, Ord coarse) =>
    (step -> coarse) -> FTA state (TraceSymbol step) annotation -> PlainFTA (Set state) (TraceSymbol coarse)
project image = projectMaybe (Just . image)

{- | 'project' with hidden steps: a step whose image is 'Nothing' is removed
from the trace. A state of the result is a set of input states that is
closed under hidden steps, so the result has one run for each trace, and the
same bound on its size as 'determinize'. Hidden steps can form a cycle. The
function does not interpret annotations.
-}
projectMaybe ::
    (Ord state, Ord coarse) =>
    (step -> Maybe coarse) -> FTA state (TraceSymbol step) annotation -> PlainFTA (Set state) (TraceSymbol coarse)
projectMaybe image automaton = subsets visible hidden (FTA.initialState automaton)
  where
    visible state = [(symbol, children) | (trace, children) <- edges automaton state, Just symbol <- [shown trace]]
    hidden state = [child | (Step step, [child]) <- edges automaton state, Nothing <- [image step]]
    shown End = Just End
    shown (Step step) = Step <$> image step

-- | The symbol and the children of each transition of a state.
edges :: (Ord state) => FTA state symbol annotation -> state -> [(symbol, [state])]
edges automaton state =
    [(transitionSymbol transition, transitionChildren transition) | transition <- FTA.transitionsFrom automaton state]

{- | The subset construction from the symbol and the children of each
transition of a state, the states that a state goes to without a step, and
an initial state. A state of the result is a set of states that contains
each state that one of its states goes to without a step. The construction
reads only 'End' with no child and 'Step' with one child.
-}
subsets ::
    (Ord state, Ord step) =>
    (state -> [(TraceSymbol step, [state])]) -> (state -> [state]) -> state -> PlainFTA (Set state) (TraceSymbol step)
subsets edgesOf silent initial =
    -- Each child is an explored set, and each symbol has one arity, so validation cannot fail.
    fromRight (error "subsets: the subset construction of trace terms is valid")
        $ FTA.mkFTA start
        $ explore row FTA.transitionChildren start
  where
    start = closure $ Set.singleton initial
    row states =
        [Transition End [] noConstraint | (End, []) `elem` outgoing]
            <> [Transition (Step step) [closure next] noConstraint | (step, next) <- Map.toList successors]
      where
        outgoing = concatMap edgesOf $ Set.toList states
        successors = Map.fromListWith Set.union [(step, Set.singleton child) | (Step step, [child]) <- outgoing]
    -- The states that a set reaches without a step.
    closure states = case Set.difference (Set.fromList $ concatMap silent $ Set.toList states) states of
        added
            | Set.null added -> states
            | otherwise -> closure $ Set.union states added
