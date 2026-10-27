{-# LANGUAGE OverloadedStrings #-}

{- | Traces of state machines over named integers, as refinement generators.

A 'GuardedMachine' has named integers as its state, with an initial value for
each name, and its steps. A 'GuardedStep' can have an integer parameter from
a range. Its guard is the precondition over the state and the parameter, and
its update gives the new values of some names. A guard and an update read the
state by name. They are functions over 'Symbolic', so one definition runs on
'Integer' values and gives a 'Bool', and runs on the terms of
"Data.CFTA.Refinement.Expression" and gives a 'Formula':

@
account :: GuardedMachine
account =
    GuardedMachine
        [("balance", 0)]
        [ GuardedStep "deposit" (Just (1, 1000000)) (\_ _ -> true) (\state amount -> [("balance", state "balance" + amount)])
        , GuardedStep "withdraw" (Just (1, 1000000)) (\state amount -> amount .<= state "balance") (\state amount -> [("balance", state "balance" - amount)])
        ]
@

'guardedTraces' gives the generator of the traces of at most @n@ steps. Each
name is a named measure of a prefix of a trace (see
'Data.CFTA.Gen.Refinement.measuredBy'): the measure of a prefix is its state.
The guard of a step is the contract of its constructor, and the update gives
its measures. A parameter is an integer from
'Data.CFTA.Gen.Refinement.every', so the compiled generator counts the
integer points of the guards and does not list the parameters. A range of a
million values costs no more than a range of two, and a parameter adds no
query to the solver.

The term of a trace has its last step at the root and the initial state as
its leaf, because a measure is calculated from the children. So the ranks
are not the ranks of "Data.CFTA.Trace", which has the first step at the root.

'guardedRun' runs a sequence of events on concrete values. 'guardedProduct'
gives the machine of the traces of two machines. 'unrolled' gives a finite
'StateMachine' for small ranges, so the operations of "Data.CFTA.Trace" apply.
-}
module Data.CFTA.Gen.Refinement.Trace (
    GuardedStep (..),
    GuardedMachine (..),
    Event (..),
    guardedTraces,
    guardedRun,
    guardedProduct,
    unrolled,
) where

import Control.Monad (guard)
import Data.List (find)
import Data.Maybe (fromMaybe, isNothing)

import Data.CFTA.Gen.Refinement (LTAGen, every, leaf, measuredBy, oneof, recurUpTo, satisfying)
import Data.CFTA.Index (Depth (..))
import Data.CFTA.Refinement.Expression (Expr, literal, uninterpreted)
import Data.CFTA.Refinement.Symbolic (Symbolic (..), true, (.&&))
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Trace (Infeasible (..), StateMachine (..), TraceSymbol (Step))

-- | A step of a 'GuardedMachine'.
data GuardedStep = GuardedStep
    { stepName :: Symbol
    -- ^ The name of the step. It is the symbol of the constructor of the step.
    , stepRange :: Maybe (Integer, Integer)
    -- ^ The lowest and the highest value of the parameter, or 'Nothing' when the step has no parameter.
    , stepGuard :: forall e. (Symbolic e) => (String -> e) -> e -> Truth e
    {- ^ The precondition, from the value of each name and the parameter. A
    step without a parameter gets the parameter 0.
    -}
    , stepUpdate :: forall e. (Symbolic e) => (String -> e) -> e -> [(String, e)]
    {- ^ The new values of some names, from the value of each name and the
    parameter. The other names keep their values.
    -}
    }

-- | A state machine over named integers.
data GuardedMachine = GuardedMachine
    { guardedInitial :: [(String, Integer)]
    {- ^ The names of the integers of the state, with their values before the
    first step. Each name is a named measure, and two names are different.
    -}
    , guardedSteps :: [GuardedStep]
    -- ^ The steps. Two steps have different names.
    }

-- | One step of a trace: the name of the step, and its parameter when it has one.
data Event = Event
    { eventStep :: Symbol
    , eventParameter :: Maybe Integer
    }
    deriving (Eq, Ord, Show)

{- | The generator of the traces of at most the given number of steps, as
lists of events from the first. Compile it with
'Data.CFTA.Gen.Refinement.compile' or 'Data.CFTA.Gen.Refinement.compileWith'.

The leaf of a term is the initial state, and each step is a constructor over
the prefix and the parameter. A step without a parameter has the parameter
0 in its term. So each step adds two to the size, and the traces of exactly
@n@ steps are the members of size @2n + 1@: 'Data.CFTA.Gen.countAtSize' of
the compiled generator at that size counts them.
-}
guardedTraces :: Int -> GuardedMachine -> LTAGen [Event]
guardedTraces bound GuardedMachine{guardedInitial, guardedSteps} =
    reverse <$> recurUpTo (Depth bound) (\prefix -> oneof (start : map (extend prefix) guardedSteps))
  where
    -- The state of a term: each name is a named measure of the term.
    stateOf :: Expr -> [(String, Expr)]
    stateOf term = [(name, uninterpreted name [term]) | (name, _) <- guardedInitial]
    start =
        leaf [] "__cfta_trace_start" $ \value ->
            foldr (.&&) true [measure .== literal initial | ((_, measure), (_, initial)) <- zip (stateOf value) guardedInitial]
    extend prefix step =
        measuredBy
            (stepName step)
            (\previous value -> stepGuard step (valueOf $ stateOf previous) value)
            [ (name, \previous value -> valueOf (afterStep step (stateOf previous) value) name)
            | (name, _) <- guardedInitial
            ]
            ((\events value -> Event (stepName step) (value <$ stepRange step) : events) <$> prefix <*> parameter step)
    parameter step =
        let (low, high) = fromMaybe (0, 0) (stepRange step)
         in every `satisfying` (\value -> literal low .<= value .&& value .<= literal high)

{- | Run a sequence of events from the initial state: the final state, or the
shortest prefix that fails. An event fails when the machine has no step with
its name, when its parameter is missing, extra, or outside the range of the
step, or when the guard of the step is false. Then 'infeasibleSymbol' is the
event, and 'infeasibleStates' holds the state before it. The guards run on
'Integer' values, so the run decides each of them.
-}
guardedRun :: GuardedMachine -> [Event] -> Either (Infeasible [(String, Integer)] Event) [(String, Integer)]
guardedRun machine = go [] (guardedInitial machine)
  where
    go _ state [] = Right state
    go done state (event : rest) = case nextState machine state event of
        Nothing -> Left $ Infeasible (reverse done) (Step event) [state]
        Just next -> go (event : done) next rest

{- | The machine of the sequences that both machines accept. Its state has the
names of the first machine and then the names of the second, so the names of
the two machines must be different. It has a step for each step name that
both machines have, with both guards and both updates. The range of its
parameter is the intersection of the two ranges, because both machines must
accept the parameter. A step name without a parameter in one machine and with
one in the other, or with ranges that do not intersect, gives no step.
-}
guardedProduct :: GuardedMachine -> GuardedMachine -> GuardedMachine
guardedProduct first second =
    GuardedMachine
        (guardedInitial first <> guardedInitial second)
        [ GuardedStep
            (stepName left)
            range
            (\state value -> stepGuard left state value .&& stepGuard right state value)
            (\state value -> stepUpdate left state value <> stepUpdate right state value)
        | left <- guardedSteps first
        , right <- take 1 [step | step <- guardedSteps second, stepName step == stepName left]
        , Just range <- [common (stepRange left) (stepRange right)]
        ]
  where
    common Nothing Nothing = Just Nothing
    common (Just (lowLeft, highLeft)) (Just (lowRight, highRight))
        | low <= high = Just $ Just (low, high)
      where
        low = max lowLeft lowRight
        high = min highLeft highRight
    common _ _ = Nothing

{- | The finite machine of the traces of at most the given number of steps:
its state is the number of steps and the state of the guarded machine. It has
an event for each step and each value of its range, so it is for small
ranges. It gives the traces of 'guardedTraces' to the operations of
"Data.CFTA.Trace".
-}
unrolled :: Int -> GuardedMachine -> StateMachine (Int, [(String, Integer)]) Event
unrolled bound machine = StateMachine (0, guardedInitial machine) events next (const True)
  where
    events =
        [ Event (stepName step) parameter
        | step <- guardedSteps machine
        , parameter <- maybe [Nothing] (\(low, high) -> map Just [low .. high]) (stepRange step)
        ]
    next (count, state) event
        | count < bound = (count + 1,) <$> nextState machine state event
        | otherwise = Nothing

-- | The state after an event on concrete values, when the event can run.
nextState :: GuardedMachine -> [(String, Integer)] -> Event -> Maybe [(String, Integer)]
nextState machine state (Event name parameter) = do
    step <- find ((== name) . stepName) (guardedSteps machine)
    value <- case (stepRange step, parameter) of
        (Nothing, Nothing) -> Just 0
        (Just (low, high), Just value) | low <= value && value <= high -> Just value
        _ -> Nothing
    guard $ stepGuard step (valueOf state) value
    Just $ afterStep step state value

-- | The state after a step: the update sets some names, and the other names keep their values.
afterStep :: (Symbolic e) => GuardedStep -> [(String, e)] -> e -> [(String, e)]
afterStep step state value = case [name | (name, _) <- changes, isNothing $ lookup name state] of
    name : _ ->
        error $ "Data.CFTA.Gen.Refinement.Trace: the step " <> show (stepName step) <> " sets the unknown name " <> show name
    [] -> [(name, fromMaybe old $ lookup name changes) | (name, old) <- state]
  where
    changes = stepUpdate step (valueOf state) value

-- | The value of a name in a state.
valueOf :: [(String, e)] -> String -> e
valueOf state name =
    fromMaybe (error $ "Data.CFTA.Gen.Refinement.Trace: no integer of the state is named " <> show name) (lookup name state)
