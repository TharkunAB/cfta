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
* 'bestTerms': the completions of the prefix with the largest probabilities;
* 'termLogProbability': the log-probability of a term.

'condition' gives the mixture given an event: the terms that a second
automaton accepts. The mixture given the event is the mixture of the
components given the event, with new shares. The queries above then read
only the terms of the event. 'eventProbability' gives the probability of the
event after a prefix, in the mixture before 'condition'. A decoder with a
lookahead needs this probability.

A mixture has no temperature: a power of a sum of probabilities is not a sum
of powers, so the terms at a temperature are not a mixture of the components
at that temperature.
-}
module Data.CFTA.Sized.Prefix.Mixture (
    Mixture,
    train,
    condition,
    nextTokenProbabilities,
    componentProbabilities,
    lowerTerm,
    sampleTerm,
    bestTerms,
    termLogProbability,
    eventProbability,
) where

import Data.Containers.ListUtils (nubOrd)
import Data.List (sortOn)
import Data.Ord (Down (..))
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
    bestCompletions,
    completionCount,
    completionWeight,
    lowerCompletions,
    nextTokens,
    prefixCompletions,
    weightOfTerm,
 )
import Data.CFTA.Sized.Prefix.Parents (
    Parented,
    Reach,
    intersectEvent,
    labelParents,
    labelPrefix,
    numbered,
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
    , mixtureAutomaton :: FTA.FTA Int (Parented symbol) Constraint
    -- ^ The labelled automaton, or its product with the events of 'condition', with the states numbered.
    , mixtureBound :: Int
    -- ^ The size bound.
    , mixturePrior :: [Component symbol]
    -- ^ The components before 'condition'.
    , mixtureComponents :: [Component symbol]
    }

-- | A component of a mixture: a share and one model.
data Component symbol = Component
    { componentShare :: Rational
    -- ^ Positive. The sum of the shares of a mixture is one.
    , componentLogWeights :: LogWeights (Parented symbol)
    , componentCompletions :: Completions (Parented symbol)
    -- ^ The completions of the empty prefix of 'mixtureAutomaton', with the weights of the component.
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
constraint, when 'distillMixture' gives no result (also when the fit is not
finite), when the completions do not accept the bound, or when
'withLogWeights' rejects the log-weights of a component.
-}
train ::
    (Ord state, Ord symbol) =>
    Reach -> FTA.FTA state symbol Constraint -> Int -> [[Term symbol]] -> Maybe (Mixture symbol)
train reach automaton bound groups = do
    labelled <- withParents reach rootContext automaton
    fitted <- distillMixture labelled bound $ map (map $ labelParents reach rootContext) groups
    let renumbered = numbered labelled
    completions <- either (const Nothing) Just $ prefixCompletions (Size $ toInteger bound) renumbered
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
    components <- traverse component fitted
    Just $ Mixture reach renumbered bound components components

{- | The mixture given an event: the terms of the mixture that the event also
accepts, each with its probability divided by the probability of the event.
The event is an automaton over the plain symbols, as for
'Data.CFTA.Sized.Prefix.Model.condition'. The mixture given the event is the
mixture of the components given the event. The new share of a component is
its share times the probability of the event in the component, over the
probability of the event in the mixture:

> P(t | E) = Σ_k share'_k P_k(t | E)
> share'_k = share_k P_k(E) / Σ_j share_j P_j(E)

The new shares are exact. The components read one product of the automaton
of the mixture and the event ('intersectEvent'), and one set of completions
of the product. A term outside the event has the probability zero, and the
queries of the result read only the terms of the event. Conditioning on two
events, one after the other, gives the mixture given both events.

'Nothing' when a transition of the event has a constraint other than
'Data.CFTA.Constraint.noConstraint'. 'Nothing' also when the event accepts no
term of the mixture within the bound.
-}
condition :: (Ord state, Ord symbol) => FTA.FTA state symbol Constraint -> Mixture symbol -> Maybe (Mixture symbol)
condition event mixture = do
    automaton <- intersectEvent event (mixtureAutomaton mixture)
    completions <- either (const Nothing) Just $ prefixCompletions (Size $ toInteger $ mixtureBound mixture) automaton
    joint <-
        if completionCount completions == 0
            then Nothing
            else traverse (given completions) (mixtureComponents mixture)
    let total = sum $ map componentShare joint
    Just
        mixture
            { mixtureAutomaton = automaton
            , mixtureComponents = [component{componentShare = componentShare component / total} | component <- joint]
            }
  where
    -- The component given the event. Its share is the share times the probability of the event in the component.
    given completions component = do
        weighted <- withLogWeights (componentLogWeights component) completions
        let weight = completionWeight weighted
        Just
            component
                { componentShare = componentShare component * weight / componentTotal component
                , componentCompletions = weighted
                , componentLogTotal = logPartition (componentLogWeights component) weighted
                , componentTotal = weight
                }

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
        Just (exactMass component $ completionWeight completions, generator)

-- | The QuickCheck generator of 'lowerTerm'.
sampleTerm :: (Ord symbol) => Mixture symbol -> [Token symbol] -> Maybe (QC.Gen (Term symbol))
sampleTerm mixture prefix = generator <$> lowerTerm mixture prefix
  where
    generator (QuickCheckBackend generated) = generated

{- | The completions of a prefix with the largest probabilities, at most the
given number, the most probable first. Each probability is among the
completions of the prefix. Completions with equal probabilities come in
ascending order of the terms. The order compares the exact probabilities, so
two completions whose probabilities give the same 'Double' keep the order of
their exact probabilities. 'Nothing' when the prefix has no completion.

The probability of a term is a sum over the components. The most probable
term of a sum is not always the most probable term of a component. So the
largest weights of each component ('bestCompletions') do not directly give
the result, and a search is necessary. The search is the threshold algorithm
of Fagin, Lotem, and Naor (/Optimal aggregation algorithms for middleware/,
2003). A round takes the @n@ completions with the largest weights in each
component. Each of these candidates gets its mass: the sum, over the
components, of the share times the weight of the term over the total weight
of the component. A term that is not a candidate has, in each component, at
most the weight of the last term of the list of the component. So its mass is
at most the bound: the sum, over the components, of the share times the
weight of the last term of the list over the total weight of the component.
The round gives the result when the lists hold every completion, or when the
candidate at the given number has a mass larger than the bound. Otherwise,
the next round takes twice as many completions. The first round takes the
given number.

The work of a round is one 'bestCompletions' in each component and, for each
candidate in each component, a product over the nodes of the candidate
('weightOfTerm'). The masses are exact 'Rational' numbers, so rounding does
not change the order or the end of the search. The lists grow when the
components put the completions in very different orders, or when many
completions have the probability of the last result. In the worst case, the
lists hold all the completions of the prefix.
-}
bestTerms :: (Ord symbol) => Int -> Mixture symbol -> [Token symbol] -> Maybe [(Term symbol, Double)]
bestTerms count mixture prefix = do
    current <- after mixture prefix
    let total = sum [exactMass component $ completionWeight completions | (component, completions) <- current]
        search n
            | complete || snd (last found) > bound = found
            | otherwise = search (2 * n)
          where
            lists = [bestCompletions n completions | (_, completions) <- current]
            -- The components have the same completions, so all the lists have the same length.
            complete = any ((< n) . length) lists
            found =
                take count $
                    sortOn
                        (\(term, value) -> (Down value, term))
                        [ ( unlabelParents term
                          , sum [exactMass component $ weightOfTerm (componentCompletions component) term | (component, _) <- current]
                          )
                        | term <- nubOrd $ map fst $ concat lists
                        ]
            bound = sum [exactMass component $ snd $ last list | ((component, _), list) <- zip current lists]
    Just $ if count <= 0 then [] else [(term, fromRational $ value / total) | (term, value) <- search count]

-- | The log-probability of a term. 'Nothing' when the term is not a term of the automaton within the bound.
termLogProbability :: (Ord symbol) => Mixture symbol -> Term symbol -> Maybe Double
termLogProbability mixture term = logSum <$> traverse part (mixtureComponents mixture)
  where
    labelled = labelParents (mixtureReach mixture) rootContext term
    part component =
        (logShare component +)
            <$> logProbability (componentLogWeights component) (componentCompletions component) labelled

{- | The probability of the event of a mixture, given that the term starts with
a prefix, in the mixture before 'condition'. The event of a mixture is the
intersection of the events of each 'condition' of the mixture. The
probability is the probability of the completions of the prefix that the
event accepts, over the probability of all the completions of the prefix, in
the mixture before 'condition':

> P(E | p) = (Σ_k share_k W_k(p, E) / Z_k) / (Σ_k share_k W_k(p) / Z_k)

Here @share_k@ and @Z_k@ are the share and the total weight of the component
@k@ before 'condition'. @W_k(p)@ is the weight of the completions of @p@ in
the component, and @W_k(p, E)@ is the weight of the completions of @p@ that
the event accepts. The probability is one for each prefix with a completion
when the mixture has no 'condition', and zero when the event accepts no
completion of the prefix. 'Nothing' when no completion of the mixture before
'condition' starts with the prefix.

With 'nextTokenProbabilities' before and after 'condition', this gives the
lookahead of constrained decoding, as
'Data.CFTA.Sized.Prefix.Model.eventProbability' gives it for a model:

> P(x | p, E) / P(x | p) = P(E | p <> [x]) / P(E | p)
-}
eventProbability :: (Ord symbol) => Mixture symbol -> [Token symbol] -> Maybe Double
eventProbability mixture prefix = do
    prior <- after mixture{mixtureComponents = mixturePrior mixture} prefix
    let total = logSum $ map (uncurry logMass) prior
    Just $ case after mixture prefix of
        Nothing -> 0
        -- The share and the total of each component before 'condition', with the completions after it.
        Just current -> exp $ logSum [logMass component completions | ((component, _), (_, completions)) <- zip prior current] - total

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

{- | The share of a component times a weight over the total weight of the
component. For the weight of some completions of the component, it is the
probability that a term of the mixture is one of these completions of the
component, as 'logMass' gives its logarithm.
-}
exactMass :: Component symbol -> Rational -> Rational
exactMass component weight = componentShare component * weight / componentTotal component

-- | The logarithm of the share of a component.
logShare :: Component symbol -> Double
logShare = log . fromRational . componentShare

-- | The logarithm of the sum of the exponentials. The list has a value.
logSum :: [Double] -> Double
logSum values = top + log (sum [exp $ value - top | value <- values])
  where
    top = maximum values
