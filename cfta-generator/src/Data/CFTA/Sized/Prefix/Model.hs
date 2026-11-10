{- | A small language model of the terms of an automaton.

A model gives each node of a term a weight that depends on the token of the
node and on its context: the nearest ancestors of the node, each with the
position of the path, and the root token of its left sibling
("Data.CFTA.Sized.Prefix.Parents"). The probability of a term within the size
bound is the product of the weights of its nodes over the total weight of
the terms within the bound, as in "Data.CFTA.Sized.Prefix.Train".

'train' fits the weights to a corpus of terms with 'distill' on the labelled
automaton ('withParents'). Each term has one labelling, so a weight of a
labelled symbol is a weight of a token in a context. With a 'Reach' of zero
ancestors and no sibling, the model has one weight for each token.

The queries take a prefix of plain tokens and are exact for the model:

* 'nextTokenProbabilities': the probability of each next token after the
  prefix;
* 'sampleTerm': a completion of the prefix, in proportion to its probability;
* 'bestTerms': the completions of the prefix with the largest probabilities;
* 'termLogProbability': the log-probability of a term.

'withTemperature' sets the temperature of whole terms ('atTemperature').
-}
module Data.CFTA.Sized.Prefix.Model (
    Model,
    train,
    trainWithReport,
    withTemperature,
    condition,
    nextTokenProbabilities,
    sampleTerm,
    bestTerms,
    termLogProbability,
) where

import qualified Data.Map.Strict as Map
import qualified Test.QuickCheck as QC

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Index (Size (..))
import Data.CFTA.Sized.Prefix (
    Completions,
    Token,
    afterPrefix,
    bestCompletions,
    completionCount,
    completionWeight,
    prefixCompletions,
 )
import Data.CFTA.Sized.Prefix.Parents (
    Parented,
    Reach,
    labelParents,
    labelPrefix,
    rootContext,
    unlabelParents,
    withParents,
 )
import Data.CFTA.Sized.Prefix.QuickCheck (sampleWeighted)
import Data.CFTA.Sized.Prefix.Train (
    DistillReport (..),
    FitReport (..),
    LogWeights,
    Step (..),
    TrainingError (..),
    atTemperature,
    distill,
    distillWithReport,
    logProbability,
    nextTokenDistribution,
    withLogWeights,
 )
import Data.CFTA.Term (Term)

-- | A model of the terms of an automaton within a size bound.
data Model symbol = Model
    { modelReach :: Reach
    , modelLogWeights :: LogWeights (Parented symbol)
    -- ^ The fitted log-weights, at the temperature one.
    , modelTemperature :: Double
    , modelAutomaton :: FTA.FTA Int (Parented symbol) Constraint
    -- ^ The labelled automaton, or its product with the events of 'condition', with the states numbered.
    , modelBound :: Int
    -- ^ The size bound.
    , modelPrior :: Completions (Parented symbol)
    -- ^ The completions of the empty prefix of the labelled automaton, before 'condition', with the weights at the temperature.
    , modelCompletions :: Completions (Parented symbol)
    -- ^ The completions of the empty prefix of 'modelAutomaton', with the weights at the temperature.
    }

{- | Fit a model with a reach to a corpus of terms of an automaton, for the
terms within a size bound, by 'distill' on the labelled automaton. The
temperature is one. 'Nothing' when the automaton has a constraint, or when
'distill' gives no weights.
-}
train ::
    (Ord state, Ord symbol) => Reach -> FTA.FTA state symbol Constraint -> Int -> [Term symbol] -> Maybe (Model symbol)
train reach automaton bound terms = do
    labelled <- withParents reach rootContext automaton
    logWeights <- distill labelled bound (map (labelParents reach rootContext) terms)
    let renumbered = numbered labelled
    completions <- either (const Nothing) Just $ prefixCompletions (Size $ toInteger bound) renumbered
    weighted <- withLogWeights logWeights completions
    Just
        Model
            { modelReach = reach
            , modelLogWeights = logWeights
            , modelTemperature = 1
            , modelAutomaton = renumbered
            , modelBound = bound
            , modelPrior = weighted
            , modelCompletions = weighted
            }

{- | Fit the same model as 'train', with the optimizer's stop reason and
retained and dropped corpus counts. The report's weights use context-labelled
symbols; model queries still use plain symbols. A finite fit can stop before
convergence. 'UnrepresentableWeights' means that its log-weights cannot be
converted to finite positive sampling potentials. Other errors come from
context labelling or 'distillWithReport'.
-}
trainWithReport ::
    (Ord state, Ord symbol) =>
    Reach ->
    FTA.FTA state symbol Constraint ->
    Int ->
    [Term symbol] ->
    Either TrainingError (Model symbol, DistillReport (Parented symbol))
trainWithReport reach automaton bound terms = do
    labelled <- maybe (Left UnsupportedTrainingLanguage) Right $ withParents reach rootContext automaton
    report <- distillWithReport labelled bound (map (labelParents reach rootContext) terms)
    let logWeights = stepWeights $ fitFinalStep $ distillFit report
    if any unrepresentable logWeights
        then Left UnrepresentableWeights
        else do
            let renumbered = numbered labelled
            completions <-
                either (const $ Left UnsupportedTrainingLanguage) Right $ prefixCompletions (Size $ toInteger bound) renumbered
            weighted <- maybe (Left UnrepresentableWeights) Right $ withLogWeights logWeights completions
            pure
                ( Model
                    { modelReach = reach
                    , modelLogWeights = logWeights
                    , modelTemperature = 1
                    , modelAutomaton = renumbered
                    , modelBound = bound
                    , modelPrior = weighted
                    , modelCompletions = weighted
                    }
                , report
                )
  where
    unrepresentable logWeight = let value = exp logWeight in isNaN value || isInfinite value || value <= 0

{- | The model at a temperature of whole terms: the probability of each term to
the power one over the temperature, renormalized ('atTemperature'). The
temperature replaces the temperature of the model. 'Nothing' when the
temperature is nonfinite or not positive, or when a scaled log-weight has
no finite positive exponential ('withLogWeights').
-}
withTemperature :: (Ord symbol) => Double -> Model symbol -> Maybe (Model symbol)
withTemperature temperature model
    | isNaN temperature || isInfinite temperature || temperature <= 0 = Nothing
    | otherwise = do
        let logWeights = atTemperature temperature $ modelLogWeights model
        prior <- withLogWeights logWeights (modelPrior model)
        weighted <- withLogWeights logWeights (modelCompletions model)
        Just model{modelTemperature = temperature, modelPrior = prior, modelCompletions = weighted}

{- | The model given an event: the terms of the model that the event also
accepts, each with its probability divided by the probability of the event.
The event is an automaton over the plain symbols. The result reads the
product of the automaton of the model and the event ('FTA.intersectWith'). A
labelled symbol matches an event symbol when its plain symbol is the event
symbol. The product keeps the labelled symbol, so each node keeps its
weight. A term outside the event has the probability zero, and the queries
of the result read only the terms of the event. Conditioning on two events,
one after the other, gives the model given both events. The temperature does
not change.

When the event accepts a term by two runs, the product also accepts it by two
runs. 'prefixCompletions' gives each term once also then, with one weight, so
the probabilities stay exact. The queries then read the bottom-up
deterministic rows of the product, or, when these have more than 1024
states, a list of the terms up to the bound.

'Nothing' when a transition of the event has a constraint other than
'noConstraint': an equality constraint compares the subterms at two paths,
and their labelled subterms have different contexts. 'Nothing' also when the
event accepts no term of the model within the bound.
-}
condition :: (Ord state, Ord symbol) => FTA.FTA state symbol Constraint -> Model symbol -> Maybe (Model symbol)
condition event model
    | any (any ((/= noConstraint) . FTA.transitionConstraint)) (FTA.transitionTable event) = Nothing
    | otherwise = do
        let automaton = numbered $ FTA.intersectWith match (\_ _ -> noConstraint) (modelAutomaton model) event
            match label symbol = if fst (fst label) == symbol then Just label else Nothing
        completions <- either (const Nothing) Just $ prefixCompletions (Size $ toInteger $ modelBound model) automaton
        weighted <- withLogWeights (logWeightsOf model) completions
        if completionCount completions == 0
            then Nothing
            else Just model{modelAutomaton = automaton, modelCompletions = weighted}

{- | The probability of each next token after a prefix, in ascending order of
the tokens. A complete prefix has no next token. 'Nothing' when no
completion starts with the prefix.
-}
nextTokenProbabilities :: (Ord symbol) => Model symbol -> [Token symbol] -> Maybe [(Token symbol, Double)]
nextTokenProbabilities model prefix = do
    completions <- after model prefix
    Just [(token, probability) | (((token, _), _), probability) <- nextTokenDistribution (logWeightsOf model) completions]

{- | A completion of a prefix, drawn in proportion to its probability.
'Nothing' when no completion starts with the prefix.
-}
sampleTerm :: (Ord symbol) => Model symbol -> [Token symbol] -> Maybe (QC.Gen (Term symbol))
sampleTerm model prefix = fmap (fmap unlabelParents) . sampleWeighted =<< after model prefix

{- | The completions of a prefix with the largest probabilities, at most the
given number, the most probable first ('bestCompletions'). Each probability
is among the completions of the prefix. 'Nothing' when no completion starts
with the prefix.
-}
bestTerms :: (Ord symbol) => Int -> Model symbol -> [Token symbol] -> Maybe [(Term symbol, Double)]
bestTerms count model prefix = do
    completions <- after model prefix
    let total = completionWeight completions
    Just [(unlabelParents term, fromRational $ value / total) | (term, value) <- bestCompletions count completions]

{- | The log-probability of a term among the terms within the bound.
'Nothing' when the automaton does not accept the term within the bound.
-}
termLogProbability :: (Ord symbol) => Model symbol -> Term symbol -> Maybe Double
termLogProbability model =
    logProbability (logWeightsOf model) (modelCompletions model) . labelParents (modelReach model) rootContext

-- | An automaton with each state renamed to its position in the ascending order of the states.
numbered :: (Ord state) => FTA.FTA state symbol constraint -> FTA.FTA Int symbol constraint
numbered automaton = FTA.mapStates (numbers Map.!) automaton
  where
    numbers = Map.fromList $ zip (FTA.states automaton) [0 ..]

-- | The log-weights of a model at its temperature.
logWeightsOf :: Model symbol -> LogWeights (Parented symbol)
logWeightsOf model = atTemperature (modelTemperature model) (modelLogWeights model)

{- | The completions of a prefix of plain tokens. The context of each node of
the prefix comes from the nodes before it ('labelPrefix').
-}
after :: (Ord symbol) => Model symbol -> [Token symbol] -> Maybe (Completions (Parented symbol))
after model prefix = afterPrefix (modelCompletions model) =<< labelPrefix (modelReach model) rootContext prefix
