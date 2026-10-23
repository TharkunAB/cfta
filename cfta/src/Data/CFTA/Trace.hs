{-# LANGUAGE DeriveFunctor #-}

{- | Trace languages: the step sequences that a description of a state
machine accepts, as the terms of a finite tree automaton.

A 'Description' has an initial state, a list of steps, the next state of a
step in a state, and the states in which a trace can end. A step can run in a
state when it has a next state there: this is the precondition of the step.
The next state is its postcondition. A trace of the steps @s1 ... sn@ is the
right spine @Step s1 (Step s2 (... (Step sn End)))@, so the preorder of the
term is the trace, and a prefix of a trace is a preorder prefix of its term.
A trace of @n@ steps has size @n + 1@.

'traceAutomaton' makes the automaton of the traces. Its states are the states
that the initial state reaches, so the state space must be finite. The
automaton has at most one transition for each state and symbol, so each trace
has one run. Thus the automaton is unambiguous, and "Data.CFTA.Sized" and the
generators of @cfta-generator@ count, rank, unrank, sample, and shrink its
traces exactly. Operations on automata apply to it: 'Data.CFTA.intersect'
gives the traces of two descriptions over one step type, and
'Data.CFTA.Lowering.lift' gives the traces whose lowering is a trace.

'feasibility' runs a sequence of steps from the root of an automaton. It
gives the shortest prefix that has no run, and the states in which its last
symbol fails.
-}
module Data.CFTA.Trace (
    TraceSymbol (..),
    Description (..),
    traceAutomaton,
    traceTerm,
    traceSteps,
    Infeasible (..),
    feasibility,
) where

import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import Data.Hashable (Hashable)
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

-- | A state machine: the precondition and the postcondition of each step over an abstract state.
data Description state step = Description
    { descriptionInitial :: state
    -- ^ The state before the first step.
    , descriptionSteps :: [step]
    -- ^ The steps.
    , descriptionNext :: state -> step -> Maybe state
    {- ^ The state after a step. 'Nothing' when the precondition of the step
    is false in the state.
    -}
    , descriptionFinal :: state -> Bool
    -- ^ Whether a trace can end in the state.
    }

{- | The automaton of the traces of a description. Each state that the initial
state reaches is a state of the automaton. A state has an 'End' leaf when it
is final, and a 'Step' transition to the next state for each step whose
precondition is true in it. A state from which no final state is reachable
keeps its row, so 'feasibility' finds the step whose precondition is false.
'FTA.trim' removes these states.
-}
traceAutomaton :: (Ord state, Ord step) => Description state step -> PlainFTA state (TraceSymbol step)
traceAutomaton Description{descriptionInitial, descriptionSteps, descriptionNext, descriptionFinal} =
    -- Each child is a reached state, and each symbol has one arity, so validation cannot fail.
    fromRight (error "traceAutomaton: the automaton of a description is valid")
        $ FTA.mkFTA descriptionInitial
        $ explore row FTA.transitionChildren descriptionInitial
  where
    row state =
        [Transition End [] noConstraint | descriptionFinal state]
            <> [ Transition (Step step) [next] noConstraint
               | step <- descriptionSteps
               , Just next <- [descriptionNext state step]
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
