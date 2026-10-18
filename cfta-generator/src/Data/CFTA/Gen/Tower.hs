{- | The test log of a language tower and the rule for an abstraction extension.

A concrete test is a term whose leaves have exact values, such as
@lit \@{ v == 5 }@. A vocabulary is a list of predicates over the value @v@.
The abstraction of a test replaces the exact value of each leaf by its cube:
the conjunction of each predicate of the vocabulary that holds at the value,
and the negation of each one that does not. Tests with the same abstraction
are one term of the language.

A spec maps abstract terms to responses. When the spec and the model disagree
on a test, the disagreement has one of two causes (Aarts and others, FM 2012):

* the spec is wrong for that term: update the spec;
* the vocabulary is too coarse: two tests with the same term have different
  responses. Add a predicate that separates them (an abstraction extension).

'refine' applies this rule to a log until the spec agrees with every test.
The candidates for a new predicate come from templates and the values in the
log, as in Liquid Types; this module does not use interpolation.
-}
module Data.CFTA.Gen.Tower (
    -- * The log
    Observation (..),
    abstract,
    evaluate,

    -- * The rule
    Verdict (..),
    classify,
    conflicts,
    separate,

    -- * The loop
    Step (..),
    Outcome (..),
    Result (..),
    refine,

    -- * The measure
    descriptionLength,
) where

import Data.List (maximumBy, minimumBy)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import qualified Data.Set as Set
import qualified Data.Text as Text

import qualified Data.CFTA.Formula as F
import Data.CFTA.Symbol (Symbol (RefinedSymbol, Symbol), symbolRefinement, symbolText, valueName)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | One test of the log: the concrete test and the response of the model.
data Observation response = Observation
    { observedTest :: !(Term Symbol)
    , observedResponse :: !response
    }
    deriving (Eq, Show)

{- | Replace the exact value of each leaf by its cube in the vocabulary. A leaf
without an exact value stays. 'Nothing' if a predicate is outside the fragment
that 'evaluate' decides.
-}
abstract :: [F.Formula] -> Term Symbol -> Maybe (Term Symbol)
abstract vocabulary (Term.Node symbol children) = do
    parts <- traverse (abstract vocabulary) children
    case exactValue symbol of
        Nothing -> Just $ Term.Node symbol parts
        Just value -> do
            truths <- traverse (evaluate value) vocabulary
            let cube = F.conjunction [if truth then predicate else F.Not predicate | (predicate, truth) <- zip vocabulary truths]
            Just $ Term.Node (RefinedSymbol (Symbol $ symbolText symbol) cube) parts

{- | Decide a predicate at a value of @v@. The fragment is integer literals,
@v@, negation, sums, differences, products, remainders by a nonzero integer
(as the @mod@ of SMT-LIB, which is not negative),
conditionals, the six relations, and the Boolean connectives. 'Nothing'
outside that fragment.
-}
evaluate :: Integer -> F.Formula -> Maybe Bool
evaluate value = formula
  where
    formula current = case current of
        F.Top -> Just True
        F.Bottom -> Just False
        F.And parts -> and <$> traverse formula parts
        F.Or parts -> or <$> traverse formula parts
        F.Not part -> not <$> formula part
        F.Atom relation left right -> compareWith relation <$> term left <*> term right
        _ -> Nothing
    term current = case current of
        F.Lit literal -> Just literal
        F.Var name | name == F.Name (Text.pack valueName) -> Just value
        F.Neg part -> negate <$> term part
        F.Add left right -> (+) <$> term left <*> term right
        F.Sub left right -> (-) <$> term left <*> term right
        F.Mul left right -> (*) <$> term left <*> term right
        F.Mod left right -> do
            divisor <- term right
            if divisor == 0 then Nothing else (`mod` abs divisor) <$> term left
        F.Ite condition yes no -> do
            truth <- formula condition
            term $ if truth then yes else no
        _ -> Nothing
    compareWith relation = case relation of
        F.Eq -> (==)
        F.Ne -> (/=)
        F.Gt -> (>)
        F.Ge -> (>=)
        F.Lt -> (<)
        F.Le -> (<=)

-- | The value of a leaf whose refinement is @v == k@.
exactValue :: Symbol -> Maybe Integer
exactValue symbol = case symbolRefinement symbol of
    F.Atom F.Eq (F.Var name) (F.Lit value) | name == F.Name (Text.pack valueName) -> Just value
    _ -> Nothing

-- | The result of the experiment of 'classify'.
data Verdict = SpecWrong | TooCoarse
    deriving (Eq, Show)

{- | The experiment of Aarts and others: the spec mispredicts the first test.
The second test has the same abstract term. If the model gives both the same
response, the spec is wrong; otherwise the vocabulary is too coarse.
-}
classify :: (Eq response) => Observation response -> Observation response -> Verdict
classify mispredicted other
    | observedResponse mispredicted == observedResponse other = SpecWrong
    | otherwise = TooCoarse

-- | The abstract terms that have tests with more than one response, with those tests.
conflicts :: (Ord response) => [F.Formula] -> [Observation response] -> [(Term Symbol, [Observation response])]
conflicts vocabulary observations =
    [ (term, members)
    | (term, members) <- Map.toList $ classes vocabulary observations
    , Set.size (Set.fromList $ map observedResponse members) > 1
    ]

{- | The predicates to add: one or two candidates that leave fewer tests
outside the majority response of their class, with the smallest two-part
description length ('totalLength'). Two candidates are also tried together,
because a pattern such as an even sum of small digits needs two predicates
before either one makes the spec shorter. The candidates are the templates
applied to every value in the log. 'Nothing' if no candidate set leaves fewer
such tests.
-}
separate ::
    (Ord response) => [Integer -> F.Formula] -> response -> [F.Formula] -> [Observation response] -> Maybe [F.Formula]
separate templates fallback vocabulary observations
    | null improving = Nothing
    | otherwise = Just $ fst $ minimumBy (comparing snd) improving
  where
    values = Set.toAscList $ Set.fromList $ concatMap (leafValues . observedTest) observations
    candidates = [template value | template <- templates, value <- values]
    sets =
        [[candidate] | candidate <- candidates]
            <> [[first, second] | (index, first) <- zip [1 :: Int ..] candidates, second <- drop index candidates]
    current = misclassified vocabulary observations
    improving =
        [ (set, (size, length set))
        | set <- sets
        , Just errors <- [misclassified (vocabulary <> set) observations]
        , Just errors < current
        , Just size <- [totalLength fallback (vocabulary <> set) observations]
        ]
    leafValues (Term.Node symbol children) = maybe id (:) (exactValue symbol) $ concatMap leafValues children

{- | The two-part description length of a vocabulary on a log: the spec that
gives each abstract term the majority response of its tests, and the
concrete tests that the spec gets wrong. A term whose majority response is
the default has no entry. 'Nothing' if the vocabulary is outside the fragment.
-}
totalLength :: (Ord response) => response -> [F.Formula] -> [Observation response] -> Maybe Int
totalLength fallback vocabulary observations = do
    abstracted <-
        traverse
            (\observation -> (,observation) <$> abstract vocabulary (observedTest observation))
            observations
    let counts =
            Map.fromListWith
                (Map.unionWith (+))
                [(term, Map.singleton (observedResponse observation) (1 :: Int)) | (term, observation) <- abstracted]
        majority = Map.map (\responses -> fst $ maximumBy (comparing snd) $ Map.toList responses) counts
        spec = Map.filter (/= fallback) majority
        wrong =
            [ observedTest observation
            | (term, observation) <- abstracted
            , Map.lookup term majority /= Just (observedResponse observation)
            ]
    Just $ descriptionLength vocabulary spec + sum (map termLength wrong)

-- | The tests outside the majority response of their class. 'Nothing' if the vocabulary is outside the fragment.
misclassified :: (Ord response) => [F.Formula] -> [Observation response] -> Maybe Int
misclassified vocabulary observations = do
    abstracted <-
        traverse
            (\observation -> (,observedResponse observation) <$> abstract vocabulary (observedTest observation))
            observations
    let counts = Map.fromListWith (Map.unionWith (+)) [(term, Map.singleton response (1 :: Int)) | (term, response) <- abstracted]
    Just $ sum [sum responses - maximum responses | responses <- Map.elems counts]

-- | The tests of the log by abstract term, in log order. Tests outside the fragment are left out.
classes :: [F.Formula] -> [Observation response] -> Map.Map (Term Symbol) [Observation response]
classes vocabulary observations =
    Map.fromListWith
        (flip (<>))
        [(term, [observation]) | observation <- observations, Just term <- [abstract vocabulary $ observedTest observation]]

-- | One step of 'refine': a new predicate, or a new response for one abstract term.
data Step response
    = Extend !F.Formula
    | Update !(Term Symbol) !response
    deriving (Eq, Show)

-- | How 'refine' ended: the spec agrees with every test, or no candidate separates a conflict.
data Outcome response
    = Agreed
    | Stuck !(Term Symbol) ![Observation response]
    deriving (Eq, Show)

-- | The vocabulary and the spec at the end of 'refine', the steps in order, and how the loop ended.
data Result response = Result
    { resultVocabulary :: ![F.Formula]
    , resultSpec :: !(Map.Map (Term Symbol) response)
    , resultSteps :: ![Step response]
    , resultOutcome :: !(Outcome response)
    }
    deriving (Eq, Show)

{- | Apply the rule to a log until the spec agrees with every test, and give
the steps. The spec maps abstract terms to responses; a term without an entry
has the default response. For each test that the spec mispredicts, the
experiment uses another test of the log with the same abstract term. If the
vocabulary is too coarse, add the predicates from 'separate', and start the
spec again, because the new predicates split the terms. Otherwise give the
term the response of the model. If no candidate separates a conflict, stop
with 'Stuck' and the tests of that abstract term.
-}
refine ::
    (Ord response) =>
    [Integer -> F.Formula] ->
    response ->
    [F.Formula] ->
    Map.Map (Term Symbol) response ->
    [Observation response] ->
    Result response
refine templates fallback = go []
  where
    go steps vocabulary spec observations = case mispredictions of
        [] -> Result vocabulary spec (reverse steps) Agreed
        (term, mispredicted) : _ ->
            let others = filter (/= mispredicted) $ Map.findWithDefault [] term grouped
                coarse = any ((== TooCoarse) . classify mispredicted) others
             in if coarse
                    then case separate templates fallback vocabulary observations of
                        Just predicates -> go (reverse (map Extend predicates) <> steps) (vocabulary <> predicates) Map.empty observations
                        Nothing -> Result vocabulary spec (reverse steps) $ Stuck term $ Map.findWithDefault [] term grouped
                    else
                        let response = observedResponse mispredicted
                         in go (Update term response : steps) vocabulary (Map.insert term response spec) observations
      where
        grouped = classes vocabulary observations
        predicted term = fromMaybe fallback $ Map.lookup term spec
        mispredictions =
            [ (term, observation)
            | (term, members) <- Map.toList grouped
            , observation <- members
            , observedResponse observation /= predicted term
            ]

{- | The size of a spec and its vocabulary, in nodes: each predicate of the
vocabulary, and each entry of the spec. An entry counts the nodes of its term;
a node also counts the nodes of the refinement of its symbol. A smaller length
means a shorter spec, as in the minimum description length of DreamCoder.
-}
descriptionLength :: [F.Formula] -> Map.Map (Term Symbol) response -> Int
descriptionLength vocabulary spec = sum (map formulaSize vocabulary) + sum (map termLength $ Map.keys spec)

-- | The nodes of a term; a node also counts the nodes of the refinement of its symbol.
termLength :: Term Symbol -> Int
termLength (Term.Node symbol children) = 1 + refinementSize + sum (map termLength children)
  where
    refinementSize = case symbolRefinement symbol of
        F.Top -> 0
        refinement -> formulaSize refinement

-- | The nodes of a formula.
formulaSize :: F.Formula -> Int
formulaSize formula = case formula of
    F.And parts -> 1 + sum (map formulaSize parts)
    F.Or parts -> 1 + sum (map formulaSize parts)
    F.Not part -> 1 + formulaSize part
    F.Atom _ left right -> 1 + valueSize left + valueSize right
    F.Forall _ part -> 1 + formulaSize part
    F.Exists _ part -> 1 + formulaSize part
    _ -> 1
  where
    valueSize value = case value of
        F.App _ arguments -> 1 + sum (map valueSize arguments)
        F.Neg part -> 1 + valueSize part
        F.Add left right -> 1 + valueSize left + valueSize right
        F.Sub left right -> 1 + valueSize left + valueSize right
        F.Mul left right -> 1 + valueSize left + valueSize right
        F.Div left right -> 1 + valueSize left + valueSize right
        F.Mod left right -> 1 + valueSize left + valueSize right
        F.Ite condition yes no -> 1 + formulaSize condition + valueSize yes + valueSize no
        F.Cast part _ -> 1 + valueSize part
        _ -> 1
