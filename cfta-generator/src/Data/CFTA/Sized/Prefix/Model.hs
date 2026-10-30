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
    withTemperature,
    nextTokenProbabilities,
    sampleTerm,
    bestTerms,
    termLogProbability,
) where

import qualified Test.QuickCheck as QC

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint)
import Data.CFTA.Index (Size (..))
import Data.CFTA.Sized.Prefix (
    Completions,
    Token,
    afterPrefix,
    bestCompletions,
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
    LogWeights,
    atTemperature,
    distill,
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
    , modelCompletions :: Completions (Parented symbol)
    -- ^ The completions of the empty prefix of the labelled automaton, with the weights at the temperature.
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
    completions <- either (const Nothing) Just $ prefixCompletions (Size $ toInteger bound) labelled
    weighted <- withLogWeights logWeights completions
    Just $ Model reach logWeights 1 weighted

{- | The model at a temperature of whole terms: the probability of each term to
the power one over the temperature, renormalized ('atTemperature'). The
temperature replaces the temperature of the model. 'Nothing' when the
temperature is not positive.
-}
withTemperature :: (Ord symbol) => Double -> Model symbol -> Maybe (Model symbol)
withTemperature temperature model
    | temperature <= 0 = Nothing
    | otherwise = do
        weighted <- withLogWeights (atTemperature temperature $ modelLogWeights model) (modelCompletions model)
        Just model{modelTemperature = temperature, modelCompletions = weighted}

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

-- | The log-weights of a model at its temperature.
logWeightsOf :: Model symbol -> LogWeights (Parented symbol)
logWeightsOf model = atTemperature (modelTemperature model) (modelLogWeights model)

{- | The completions of a prefix of plain tokens. The context of each node of
the prefix comes from the nodes before it ('labelPrefix').
-}
after :: (Ord symbol) => Model symbol -> [Token symbol] -> Maybe (Completions (Parented symbol))
after model prefix = afterPrefix (modelCompletions model) =<< labelPrefix (modelReach model) rootContext prefix
