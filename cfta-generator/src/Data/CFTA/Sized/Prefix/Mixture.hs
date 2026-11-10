{- | A mixture of the models of "Data.CFTA.Sized.Prefix.Model".

A 'Data.CFTA.Sized.Prefix.Model.Model' has one table of weights, and the
context of a weight is bounded. So a model cannot hold a property of the
whole term. For example, when the leaves of each term of a corpus are all
@x@ or all @y@, a model learns only that the two leaves have the same
frequency, and it gives a term with the two leaves a large probability.

A mixture has a list of components. Each component has a share and one table
of weights. The probability of a term is the sum, over the components, of the
share of the component times the probability of the term in the component:

> P(t) = Σ_k share_k P_k(t)

The component of a term is hidden: no query gives it, and a term can have a
probability in each component. For the corpus of the example, one component
learns the terms with @x@ and one component learns the terms with @y@.

'train' fits the components to a corpus with 'distillMixture' on the labelled
automaton. The caller splits the corpus into groups, and each group gives
the first estimate of one component. The components have one count table.

The queries take a prefix of plain tokens and are exact for the mixture:

* 'nextTokenProbabilities': the probability of each next token after the
  prefix;
* 'componentProbabilities': the probability of each component after the
  prefix;
* 'sampleTerm' and 'lowerTerm': a completion of the prefix, in proportion to
  its probability;
* 'termLogProbability': the log-probability of a term.

A mixture has no temperature: a power of a sum of probabilities is not a sum
of powers, so the terms at a temperature are not a mixture of the components
at that temperature.
-}
module Data.CFTA.Sized.Prefix.Mixture (
    Mixture,
    train,
    nextTokenProbabilities,
    componentProbabilities,
    lowerTerm,
    sampleTerm,
    termLogProbability,
) where

import qualified Test.QuickCheck as QC

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint)
import Data.CFTA.Index (Size (..))
import Data.CFTA.Ranked (GenBackend (..))
import Data.CFTA.Ranked.Internal.Sampler (integerMasses)
import Data.CFTA.Ranked.QuickCheck (QuickCheckBackend (..))
import Data.CFTA.Sized.Prefix (
    Completions,
    Token,
    afterPrefix,
    afterToken,
    completionWeight,
    lowerCompletions,
    nextTokens,
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
import Data.CFTA.Sized.Prefix.Train (
    LogWeights,
    distillMixture,
    logPartition,
    logProbability,
    withLogWeights,
 )
import Data.CFTA.Term (Term)

-- | A mixture of models of the terms of an automaton within a size bound. It has one component or more.
data Mixture symbol = Mixture
    { mixtureReach :: Reach
    , mixtureComponents :: [Component symbol]
    }

-- | A component of a mixture: a share and one model.
data Component symbol = Component
    { componentShare :: Rational
    -- ^ Positive. The sum of the shares of a mixture is one.
    , componentLogWeights :: LogWeights (Parented symbol)
    , componentCompletions :: Completions (Parented symbol)
    -- ^ The completions of the empty prefix in the labelled automaton, with the weights of the component.
    , componentLogTotal :: Double
    -- ^ The logarithm of the total weight of the completions.
    , componentTotal :: Rational
    -- ^ The total weight of the completions.
    }

{- | Fit a mixture with the given reach to a corpus of terms that the caller
splits into groups, for the terms of the automaton within the size bound.
Each group gives the first estimate of one component, and the fit can move a
term to another component ('distillMixture'). The result depends on the
split, and the fit can stop while the components are near the split. So use a
split that separates the terms by the property that the mixture must learn.
The work of the fit can be many times the work of
'Data.CFTA.Sized.Prefix.Model.train'. The components keep the order of their
groups. With one group, the mixture is the model of
'Data.CFTA.Sized.Prefix.Model.train'. 'Nothing' when the automaton has a
constraint, when 'distillMixture' gives no result, or when the completions do
not accept the bound.
-}
train ::
    (Ord state, Ord symbol) =>
    Reach -> FTA.FTA state symbol Constraint -> Int -> [[Term symbol]] -> Maybe (Mixture symbol)
train reach automaton bound groups = do
    labelled <- withParents reach rootContext automaton
    fitted <- distillMixture labelled bound $ map (map $ labelParents reach rootContext) groups
    completions <- either (const Nothing) Just $ prefixCompletions (Size $ toInteger bound) labelled
    let total = sum $ map (toRational . fst) fitted
        component (share, logWeights) = do
            weighted <- withLogWeights logWeights completions
            Just $
                Component
                    (toRational share / total)
                    logWeights
                    weighted
                    (logPartition logWeights weighted)
                    (completionWeight weighted)
    Mixture reach <$> traverse component fitted

{- | The next tokens after a prefix, each with its probability: the
probability that a term of the mixture with this prefix continues with the
token. The tokens are in ascending order. 'Nothing' when the prefix has no
completion.
-}
nextTokenProbabilities :: (Ord symbol) => Mixture symbol -> [Token symbol] -> Maybe [(Token symbol, Double)]
nextTokenProbabilities mixture prefix = do
    current@((_, offered) : _) <- after mixture prefix
    let total = logSum $ map (uncurry logMass) current
    Just
        [ (plain, exp $ logSum masses - total)
        | (token@((plain, _), _), _) <- nextTokens offered
        , let masses =
                [ logMass component next
                | (component, completions) <- current
                , Just next <- [afterToken completions token]
                ]
        ]

{- | The probability of each component after a prefix: the probability that a
term of the mixture with this prefix is a term of the component. The empty
prefix gives the shares. 'Nothing' when the prefix has no completion.
-}
componentProbabilities :: (Ord symbol) => Mixture symbol -> [Token symbol] -> Maybe [Double]
componentProbabilities mixture prefix = do
    masses <- map (uncurry logMass) <$> after mixture prefix
    let total = logSum masses
    Just [exp $ mass - total | mass <- masses]

{- | A generator of the completions of a prefix, in a sampler backend. A
completion has its probability in the mixture, given the prefix. The
generator selects a component with its exact probability after the prefix,
and then a completion of the component. 'Nothing' when the prefix has no
completion.
-}
lowerTerm :: (GenBackend gen, Ord symbol) => Mixture symbol -> [Token symbol] -> Maybe (gen (Term symbol))
lowerTerm mixture prefix = do
    current <- after mixture prefix
    fmap unlabelParents . frequencyGen . integerMasses <$> traverse choice current
  where
    choice (component, completions) = do
        generator <- lowerCompletions completions
        Just (componentShare component * completionWeight completions / componentTotal component, generator)

-- | The QuickCheck generator of 'lowerTerm'.
sampleTerm :: (Ord symbol) => Mixture symbol -> [Token symbol] -> Maybe (QC.Gen (Term symbol))
sampleTerm mixture prefix = generator <$> lowerTerm mixture prefix
  where
    generator (QuickCheckBackend generated) = generated

-- | The log-probability of a term. 'Nothing' when the term is not a term of the automaton within the bound.
termLogProbability :: (Ord symbol) => Mixture symbol -> Term symbol -> Maybe Double
termLogProbability mixture term = logSum <$> traverse part (mixtureComponents mixture)
  where
    labelled = labelParents (mixtureReach mixture) rootContext term
    part component =
        (logShare component +)
            <$> logProbability (componentLogWeights component) (componentCompletions component) labelled

-- | The completions of a prefix in each component. 'Nothing' when the prefix has no completion.
after ::
    (Ord symbol) => Mixture symbol -> [Token symbol] -> Maybe [(Component symbol, Completions (Parented symbol))]
after mixture prefix = do
    labelled <- labelPrefix (mixtureReach mixture) rootContext prefix
    traverse
        (\component -> (,) component <$> afterPrefix (componentCompletions component) labelled)
        (mixtureComponents mixture)

{- | The logarithm of the share of a component times the probability of the
completions in the component: the probability that a term of the mixture is
one of these completions of the component.
-}
logMass :: (Ord symbol) => Component symbol -> Completions (Parented symbol) -> Double
logMass component completions =
    logShare component + logPartition (componentLogWeights component) completions - componentLogTotal component

-- | The logarithm of the share of a component.
logShare :: Component symbol -> Double
logShare = log . fromRational . componentShare

-- | The logarithm of the sum of the exponentials. The list has a value.
logSum :: [Double] -> Double
logSum values = top + log (sum [exp $ value - top | value <- values])
  where
    top = maximum values
