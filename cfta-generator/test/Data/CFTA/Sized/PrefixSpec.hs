module Data.CFTA.Sized.PrefixSpec (spec) where

import Control.Monad (ap, forM_)
import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import Data.Functor (void)
import Data.List (genericLength, inits, isPrefixOf, sortOn)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Ord (Down (..))
import Data.Ratio (denominator)
import qualified Data.Text as Text
import Test.Hspec (Spec, describe, it, shouldBe)
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Gen as QCGen
import qualified Test.QuickCheck.Random as QCRandom

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, Guard (..), equalityConstraint, noConstraint, semanticConstraint)
import qualified Data.CFTA.Equality as ECTA
import Data.CFTA.Gen.Internal.Table (unambiguousRows)
import Data.CFTA.Gen.TypedArithmeticLanguage (ArithType, arithAutomaton)
import Data.CFTA.Gen.Typing (TypingState)
import Data.CFTA.Gen.UntypedExpressionLanguage (expressionAutomaton)
import Data.CFTA.Generic (Constructor (..))
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Rank (..), Size (..))
import Data.CFTA.Refinement.Verdict (Entailment (Entailment), Verdict (..))
import Data.CFTA.Sized (SizedError (..), countOfSize, sized, sizedStates, termsOfSize, unrankOfSize)
import Data.CFTA.Sized.Prefix
import Data.CFTA.Sized.Prefix.Parents (
    Context (..),
    Reach (..),
    labelParents,
    labelPrefix,
    rootContext,
    unlabelParents,
    withParents,
 )
import Data.CFTA.Sized.Prefix.QuickCheck (sampleCompletion)
import Data.CFTA.SizedSpec (automatonGraph)
import Data.CFTA.Symbol (Symbol (Symbol))
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec = describe "Data.CFTA.Sized.Prefix" $ do
    it "lists, counts, ranks, and unranks the completions of random automata in the order of sized"
        $ QC.withNumTests 200
        $ prefixLaws . automatonGraph
    it "has unambiguous and ambiguous fixtures" $
        [unambiguous expressionAutomaton, unambiguous overlapping, unambiguous (arithAutomaton 2)]
            `shouldBe` [True, False, True]
    it "counts the terms of the fixtures up to the bound" $
        [ completionCount $ start sizeBound expressionAutomaton
        , completionCount $ start sizeBound overlapping
        , completionCount $ start sizeBound (arithAutomaton 2)
        ]
            `shouldBe` [74, 50, 32]
    it "counts a term with two runs once" $
        -- Each term f(..(a)) has a run through p and a run through q, so a sum
        -- over the stacks gives 15.
        fmap completionCount (afterToken (start sizeBound overlapping) (sym "f", 1)) `shouldBe` Just 10
    fixture "untyped expressions" expressionAutomaton
    fixture "overlapping alternatives" overlapping
    fixture "a symbol at two arities" mixedArities
    fixture "a symbol with three children" threeChildren
    fixture "typed arithmetic" (arithAutomaton 2)
    it "counts the terms of the fixtures with equality constraints up to their bounds" $
        [completionCount $ start sizeBound equalPairs, completionCount $ start 7 equalArithmetic] `shouldBe` [4, 38]
    fixture "equal pairs" equalPairs
    describe "walks the prefixes of automata with equality constraints as the listed completions, without a solver" $
        forM_ [("", Nothing), (", with the product at once", Just 0), (", with the product after one filling", Just 1)] $
            \(route, cap) -> do
                it ("on equal pairs" <> route) $ walksAsListing (maybe deciding decidingWithCap cap) 6 equalPairs
                it ("on equal sums" <> route) $ walksAsListing (maybe deciding decidingWithCap cap) 7 equalSums
                it ("on typed arithmetic with equal operands and branches, with three children" <> route)
                    $ walksAsListing (maybe deciding decidingWithCap cap) 7
                    $ FTA.mapSymbols (Symbol . Text.pack . show) equalArithmetic
    fixtureUpTo 7 "typed arithmetic with equal operands and branches" equalArithmetic
    it "offers only the equal child after the first child of a pair" $ do
        let completions = start sizeBound equalPairs
        fmap nextTokens (afterPrefix completions [(sym "g", 2), (sym "b", 0)]) `shouldBe` Just [((sym "b", 0), 1)]
        isJust (afterPrefix completions [(sym "g", 2), (sym "b", 0), (sym "a", 0)]) `shouldBe` False
    it "rejects a guard beyond equality constraints" $ do
        let different = semanticConstraint $ Not $ Same (ECTA.path [0]) (ECTA.path [1])
            guarded = automaton "s" [("s", [FTA.Transition (sym "g") ["q", "q"] different]), ("q", [leaf "a", leaf "b"])]
        either Just (const Nothing) (prefixCompletions 6 guarded) `shouldBe` Just ResidualGuard
    it "draws the sizes of two children with their weights" $ do
        -- Up to nine nodes, the two children of a sum can have one and five
        -- nodes or three and three, whose weights differ.
        let completions = start 9 expressionAutomaton
            add = fromMaybe (error "no sum") $ afterToken completions ("add", 2)
            listed = concat [termsOfSize (either (error . show) id $ sized expressionAutomaton) (Size size) | size <- [1 .. 9]]
            sums = [term | term <- listed, take 1 (preorder term) == [("add", 2)]]
        forM_ [const 1, \symbol -> if symbol == "one" then 3 else 1 / 2] $ \each -> do
            let total = sum $ map (termWeight each) sums
            fmap distribution (drawCompletion proportional $ weightedBy each add)
                `shouldBe` Just (Map.fromListWith (+) [(term, termWeight each term / total) | term <- sums])
    it "keeps a token whose completions have the weight zero, with the probability zero" $ do
        let completions = weightedBy (\symbol -> if symbol == "one" then 0 else 1) $ start 3 expressionAutomaton
            one = fromMaybe (error "no one") $ afterToken completions ("one", 0)
        lookup ("one", 0) (nextTokenWeights completions) `shouldBe` Just 0
        tokenProbability completions ("one", 0) `shouldBe` Just 0
        (completionWeight one, tokenProbability one ("zero", 0), isJust $ drawCompletion proportional one)
            `shouldBe` (0, Nothing, False)
        (weightedTotal one, rankWeighted one (Term.Node "one" []), unrankWeighted one 0) `shouldBe` (0, Just (0, 0), Nothing)
    it "rejects a negative weight" $
        isJust (withWeights (\symbol -> if symbol == "one" then -1 else 1) $ start 3 expressionAutomaton) `shouldBe` False
    it "has no completion below size one" $ do
        let completions = start 0 expressionAutomaton
        completionCount completions `shouldBe` 0
        map fst (nextTokens completions) `shouldBe` []
        isComplete completions `shouldBe` False
        isJust (sampleCompletion completions) `shouldBe` False

-- | The checks of the completions of an automaton up to 'sizeBound'.
fixture :: (Ord state, Ord symbol, Show symbol) => String -> FTA.FTA state symbol Constraint -> Spec
fixture = fixtureUpTo sizeBound

{- | The checks of the completions of an automaton up to a bound, each against
the accepted terms that 'termsOfSize' lists.
-}
fixtureUpTo ::
    forall state symbol.
    (Ord state, Ord symbol, Show symbol) =>
    Integer -> String -> FTA.FTA state symbol Constraint -> Spec
fixtureUpTo bound name graph = describe name $ do
    it "lists the size classes in order for the empty prefix" $
        completionTerms empty `shouldBe` accepted
    it "offers each next token with the number of accepted terms that start with the prefix and the token" $
        forM_ prefixes $ \prefix ->
            (prefix, nextTokens <$> afterPrefix empty prefix)
                `shouldBe` ( prefix
                           , Just
                                $ Map.toList
                                $ Map.fromListWith
                                    (+)
                                    [(tokens !! length prefix, 1) | tokens <- preorders, prefix `isPrefixOf` tokens, length tokens > length prefix]
                           )
    it "rejects each other token, and no accepted term starts with the prefix and the token" $
        forM_ prefixes $ \prefix -> do
            let completions = after prefix
                offered = map fst $ nextTokens completions
            ( prefix
                , [(token, isJust $ afterToken completions token, brute $ prefix <> [token]) | token <- alphabet, token `notElem` offered]
                )
                `shouldBe` (prefix, [(token, False, 0) | token <- alphabet, token `notElem` offered])
    it "counts the completions as the offered counts, and one more for a complete prefix" $
        forM_ prefixes $ \prefix -> do
            let completions = after prefix
                complete = if isComplete completions then 1 else 0
            (prefix, completionCount completions, sum (map snd $ nextTokens completions) + complete)
                `shouldBe` (prefix, Cardinality $ brute prefix, Cardinality $ brute prefix)
    it "is complete exactly when the prefix is an accepted term" $
        forM_ prefixes $ \prefix ->
            (prefix, isComplete $ after prefix) `shouldBe` (prefix, prefix `elem` preorders)
    it "lists, ranks, and unranks the completions in the order of sized, each once, accepted and with the prefix" $
        forM_ prefixes $ \prefix -> do
            let completions = after prefix
                listed = completionTerms completions
                count = genericLength listed
            (prefix, listed) `shouldBe` (prefix, [term | term <- accepted, prefix `isPrefixOf` preorder term])
            (prefix, completionCount completions) `shouldBe` (prefix, Cardinality count)
            (prefix, map (unrankCompletion completions . Rank) [-1 .. count])
                `shouldBe` (prefix, [Nothing] <> map Just listed <> [Nothing])
            (prefix, map (rankCompletion completions) listed) `shouldBe` (prefix, map (Just . Rank) [0 .. count - 1])
            (prefix, [term | term <- accepted, isJust (rankCompletion completions term), not (prefix `isPrefixOf` preorder term)])
                `shouldBe` (prefix, [])
            (prefix, filter (\term -> not (FTA.accepts plain term && prefix `isPrefixOf` preorder term)) listed)
                `shouldBe` (prefix, [])
    it "samples completions with the prefix, the same for the same seed" $
        forM_ prefixes $ \prefix -> do
            let completions = after prefix
                draw gen = QCGen.unGen (QC.vectorOf 20 gen) (QCRandom.mkQCGen 20261023) 30
            case sampleCompletion completions of
                Nothing -> (prefix, completionCount completions) `shouldBe` (prefix, 0)
                Just gen -> do
                    (prefix, draw gen) `shouldBe` (prefix, draw gen)
                    (prefix, filter (`notElem` completionTerms completions) (draw gen)) `shouldBe` (prefix, [])
    it "reads the classes that sized gives with each state as the initial state" $
        forM_ (Map.keys $ FTA.transitionTable $ FTA.trim graph) $ \state -> do
            let shared = either (error . show) id (sizedStates graph) state
                alone =
                    either (error . show) id
                        $ sized
                        $ fromRight (error "a state of a valid automaton is a valid initial state")
                        $ FTA.mkFTA state (Map.toList $ FTA.transitionTable graph)
            forM_ [1 .. bound] $ \size -> do
                let Cardinality count = countOfSize alone (Size size)
                    classOf found = (termsOfSize found (Size size), [unrankOfSize found (Size size) (ClassRank rank) | rank <- [-1 .. count]])
                (size, countOfSize shared (Size size), classOf shared) `shouldBe` (size, Cardinality count, classOf alone)
    it "rejects invalid prefixes" $
        forM_ invalid $ \prefix -> do
            (prefix, isJust $ afterPrefix empty prefix) `shouldBe` (prefix, False)
            (prefix, brute prefix) `shouldBe` (prefix, 0)
    describe "weights" $ do
        it "gives each next token the number of its completions as its weight, with the weight one" $
            forM_ prefixes $ \prefix -> do
                let completions = after prefix
                (prefix, nextTokenWeights completions, completionWeight completions)
                    `shouldBe` ( prefix
                               , [(token, fromIntegral count) | (token, Cardinality count) <- nextTokens completions]
                               , fromIntegral $ brute prefix
                               )
        it "gives each next token the sum of the weights of its completions" $
            forM_ prefixes $ \prefix -> do
                let completions = weightedBy weight $ after prefix
                (prefix, nextTokenWeights completions, completionWeight completions)
                    `shouldBe` ( prefix
                               , [(token, bruteWeight (prefix <> [token])) | (token, _) <- nextTokens completions]
                               , bruteWeight prefix
                               )
        it "draws each completion with its weight over the total weight" $
            forM_ prefixes $ \prefix -> forM_ [const 1, weight] $ \each -> do
                let completions = weightedBy each $ after prefix
                    total = sum [termWeight each term | term <- accepted, prefix `isPrefixOf` preorder term]
                (prefix, fmap distribution $ drawCompletion proportional completions)
                    `shouldBe` ( prefix
                               , Just $
                                    Map.fromListWith
                                        (+)
                                        [ (term, termWeight each term / total)
                                        | term <- accepted
                                        , prefix `isPrefixOf` preorder term
                                        , termWeight each term > 0
                                        ]
                               )
        it "gives the completions with the largest weights, the largest first, each once with its weight" $
            forM_ prefixes $ \prefix -> forM_ [1, 3, 1000] $ \count -> do
                let best = bestCompletions count $ weightedBy weight $ after prefix
                    completions = [term | term <- accepted, prefix `isPrefixOf` preorder term]
                (prefix, count, map snd best) `shouldBe` (prefix, count, take count $ sortOn Down $ map (termWeight weight) completions)
                (prefix, count, [term | (term, value) <- best, term `notElem` completions || termWeight weight term /= value])
                    `shouldBe` (prefix, count, [])
                (prefix, count, length (nubOrd $ map fst best)) `shouldBe` (prefix, count, length best)
        it "gives the next tokens and the complete prefix probabilities that sum to one" $
            forM_ prefixes $ \prefix -> do
                let completions = weightedBy weight $ after prefix
                    complete = sum [termWeight weight term | term <- accepted, preorder term == prefix]
                ( prefix
                    , fmap (+ complete / bruteWeight prefix) $ sum <$> traverse (tokenProbability completions . fst) (nextTokens completions)
                    )
                    `shouldBe` (prefix, Just 1)
                ( prefix
                    , [ token
                      | token <- alphabet
                      , token `notElem` map fst (nextTokens completions)
                      , tokenProbability completions token /= Just 0
                      ]
                    )
                    `shouldBe` (prefix, [])
        it "gives each completion the interval of its rank, with the weight one" $
            forM_ prefixes $ \prefix -> do
                let completions = after prefix
                    count = brute prefix
                (prefix, weightedTotal completions) `shouldBe` (prefix, count)
                (prefix, map (unrankWeighted completions) [-1 .. count])
                    `shouldBe` (prefix, [Nothing] <> map (unrankCompletion completions . Rank) [0 .. count - 1] <> [Nothing])
                (prefix, map (rankWeighted completions) $ completionTerms completions)
                    `shouldBe` (prefix, [Just (rank, 1) | rank <- [0 .. count - 1]])
                (prefix, [term | term <- accepted, isJust (rankWeighted completions term), not (prefix `isPrefixOf` preorder term)])
                    `shouldBe` (prefix, [])
        it "tiles the integers below the weighted total with the intervals of the completions in order" $
            forM_ prefixes $ \prefix -> do
                let completions = weightedBy weight $ after prefix
                    listed = completionTerms completions
                    common = foldr (lcm . denominator . weight) 1 $ completionSymbols completions
                    scale = fromInteger $ common ^ bound
                    widths = [termWeight weight term * scale | term <- listed]
                    intervals = map (rankWeighted completions) listed
                    total = weightedTotal completions
                (prefix, [(toRational offset, toRational width) | Just (offset, width) <- intervals])
                    `shouldBe` (prefix, zip (scanl (+) 0 widths) widths)
                (prefix, toRational total, completionWeight completions * scale) `shouldBe` (prefix, sum widths, sum widths)
                ( prefix
                    , [unrankWeighted completions value | Just (offset, width) <- intervals, width > 0, value <- [offset, offset + width - 1]]
                    )
                    `shouldBe` (prefix, [Just term | (term, width) <- zip listed widths, width > 0, _ <- [(), ()]])
                (prefix, map (unrankWeighted completions) [-1, total]) `shouldBe` (prefix, [Nothing, Nothing])
    -- An automaton with constraints has no labelled automaton.
    it "labels each node with its ancestors and its left sibling, one labelling for each term" $
        forM_ reaches $ \reach -> forM_ (withParents reach rootContext graph) $ \labelled -> do
            let labelledClasses = either (error . show) id $ sized labelled
                labelledTerms = concat [termsOfSize labelledClasses (Size size) | size <- [1 .. bound]]
                completions = start bound labelled
            (reach, [countOfSize labelledClasses (Size size) | size <- [1 .. bound]])
                `shouldBe` (reach, [countOfSize classes (Size size) | size <- [1 .. bound]])
            (reach, [term | term <- accepted, labelParents reach rootContext term `notElem` labelledTerms]) `shouldBe` (reach, [])
            (reach, [term | term <- map unlabelParents labelledTerms, term `notElem` accepted]) `shouldBe` (reach, [])
            forM_ prefixes $ \prefix ->
                (reach, prefix, fmap completionCount . afterPrefix completions =<< labelPrefix reach rootContext prefix)
                    `shouldBe` (reach, prefix, Just (Cardinality (brute prefix)))
    it "weighs each node by its symbol and its context in the labelled automaton" $
        forM_ [Reach 1 False, Reach 0 True] $ \reach -> forM_ (withParents reach rootContext graph) $ \labelled -> do
            let labelledEmpty = start bound labelled
            forM_ prefixes $ \prefix -> do
                let byContext ((symbol, count), Context ancestors left) =
                        weight symbol
                            * fromIntegral (count + 1)
                            * fromIntegral (1 + sum [position + 1 | (_, position) <- ancestors])
                            * maybe 1 (const 2) left
                    labelledPrefix = fromMaybe (error "a prefix of a term") $ labelPrefix reach rootContext prefix
                    completions = weightedBy byContext $ fromMaybe (error "a prefix of a term") $ afterPrefix labelledEmpty labelledPrefix
                    common = foldr (lcm . denominator . byContext) 1 $ completionSymbols completions
                (reach, prefix, completionWeight completions, toRational (weightedTotal completions))
                    `shouldBe` ( reach
                               , prefix
                               , sum [termWeight byContext (labelParents reach rootContext term) | term <- accepted, prefix `isPrefixOf` preorder term]
                               , completionWeight completions * fromInteger (common ^ bound)
                               )
  where
    plain = FTA.dropConstraints graph
    empty = start bound graph
    reaches = [Reach 1 False, Reach 0 True, Reach 2 True]
    after prefix = fromMaybe (error $ "no completions after " <> show prefix) $ afterPrefix empty prefix
    classes = either (error . show) id $ sized graph
    accepted = concat [termsOfSize classes (Size size) | size <- [1 .. bound]]
    preorders = map preorder accepted
    prefixes = nubOrd $ concatMap inits preorders
    brute :: [(symbol, Int)] -> Integer
    brute prefix = genericLength $ filter (prefix `isPrefixOf`) preorders
    -- A weight for each symbol: its place among the symbols, over three.
    symbols = nubOrd $ map fst alphabet
    weight symbol = maybe 0 (\place -> fromIntegral (place + 1) / 3) $ lookup symbol $ zip symbols [0 :: Int ..]
    bruteWeight prefix = sum [termWeight weight term | term <- accepted, prefix `isPrefixOf` preorder term]
    -- Each token of the automaton, and each symbol with one more child.
    alphabet =
        nubOrd $
            concat
                [ [(FTA.transitionSymbol transition, arity), (FTA.transitionSymbol transition, arity + 1)]
                | transition <- concat $ Map.elems $ FTA.transitionTable graph
                , let arity = length $ FTA.transitionChildren transition
                ]
    -- A wrong token after a prefix, a token after a complete term, and a
    -- term above the bound.
    invalid =
        take 5 [prefix <> [token] | prefix <- prefixes, token <- alphabet, token `notElem` map fst (nextTokens $ after prefix)]
            <> take 3 [tokens <> [token] | tokens <- preorders, token <- alphabet]
            <> take 3 (map preorder $ termsOfSize classes (Size $ bound + 1))

-- | The weight of a term: the product of the weights of its symbols.
termWeight :: (symbol -> Rational) -> Term symbol -> Rational
termWeight weight = foldr ((*) . weight) 1

-- | A distribution over values, as a list of values with their probabilities.
newtype Distribution value = Distribution [(value, Rational)]

instance Functor Distribution where
    fmap f (Distribution weighted) = Distribution [(f value, probability) | (value, probability) <- weighted]

instance Applicative Distribution where
    pure value = Distribution [(value, 1)]
    (<*>) = ap

instance Monad Distribution where
    Distribution weighted >>= next =
        Distribution
            [ (result, probability * probability')
            | (value, probability) <- weighted
            , let Distribution results = next value
            , (result, probability') <- results
            ]

-- | The choice of an index in proportion to the weights.
proportional :: [Rational] -> Distribution Int
proportional weights = Distribution [(index, weight / sum weights) | (index, weight) <- zip [0 ..] weights, weight > 0]

-- | The probability of each value of a distribution.
distribution :: (Ord value) => Distribution value -> Map.Map value Rational
distribution (Distribution weighted) = Map.fromListWith (+) weighted

-- | The largest size of the completions.
sizeBound :: Integer
sizeBound = 6

{- | The laws of the completions of an automaton for each prefix of its terms
up to a bound, against the terms that 'sized' lists: the completions in
order, their count and their ranks, the counts of the next tokens, and the
tokens that 'afterToken' rejects.
-}
prefixLaws :: (Ord state) => FTA.FTA state Symbol Constraint -> QC.Property
prefixLaws graph =
    QC.conjoin
        [ QC.counterexample (show prefix) $ case afterPrefix empty prefix of
            Nothing -> QC.counterexample "no completions" False
            Just completions ->
                let listed = completionTerms completions
                    expected = [term | term <- accepted, prefix `isPrefixOf` preorder term]
                    complete = if isComplete completions then 1 else 0
                    continues token = any (((prefix <> [token]) `isPrefixOf`) . preorder) expected
                 in listed
                        QC.=== expected
                        QC..&&. completionCount completions
                            QC.=== genericLength expected
                        QC..&&. map (rankCompletion completions) listed
                            QC.=== map (Just . Rank) [0 .. genericLength listed - 1]
                        QC..&&. sum (map snd $ nextTokens completions) + complete
                            QC.=== completionCount completions
                        QC..&&. [token | token <- alphabet, isJust (afterToken completions token) /= continues token]
                            QC.=== []
        | prefix <- nubOrd $ concatMap (inits . preorder) accepted
        ]
  where
    bound = 5
    empty = start bound graph
    accepted = concat [termsOfSize (either (error . show) id $ sized graph) (Size size) | size <- [1 .. bound]]
    alphabet =
        nubOrd
            [ (FTA.transitionSymbol transition, arity)
            | transition <- concat $ Map.elems $ FTA.transitionTable graph
            , arity <- [0 .. 2]
            ]

-- | The completions with weights that must not be negative.
weightedBy :: (symbol -> Rational) -> Completions symbol -> Completions symbol
weightedBy weight = fromMaybe (error "a negative weight") . withWeights weight

-- | The completions of the empty prefix up to a bound.
start :: (Ord state, Ord symbol) => Integer -> FTA.FTA state symbol Constraint -> Completions symbol
start bound = either (error . show) id . prefixCompletions (Size bound)

-- | Whether the rows of an automaton are unambiguous.
unambiguous :: (Ord state, Ord symbol) => FTA.FTA state symbol Constraint -> Bool
unambiguous = unambiguousRows . Map.map (map void) . FTA.transitionTable

-- | The tokens of a term in preorder.
preorder :: Term symbol -> [(symbol, Int)]
preorder (Term.Node symbol children) = (symbol, length children) : concatMap preorder children

{- | The recursive pairs of "Data.CFTA.Gen.Equality.RecursiveGenSpec", with a
second leaf: the two children of a pair are equal.
-}
equalPairs :: FTA.FTA String Symbol Constraint
equalPairs = automaton "s" [("s", [leaf "a", leaf "b", FTA.Transition (sym "g") ["s", "s"] equal])]
  where
    equal = equalityConstraint $ ECTA.mkEqConstraints [[ECTA.path [0], ECTA.path [1]]]

{- | The typed arithmetic, as in "Data.CFTA.Gen.TypingSpec", with equal
operands of a sum and equal branches of a conditional.
-}
equalArithmetic :: FTA.FTA (TypingState ArithType) Constructor Constraint
equalArithmetic = FTA.annotate annotation (arithAutomaton 2)
  where
    annotation _ transition = case constructorName $ FTA.transitionSymbol transition of
        "Plus" -> equal 0 1
        "If" -> equal 1 2
        _ -> noConstraint
    equal left right = equalityConstraint $ ECTA.mkEqConstraints [[ECTA.path [left], ECTA.path [right]]]

-- | The untyped expressions over symbols, with equal operands of a sum.
equalSums :: FTA.FTA String Symbol Constraint
equalSums =
    automaton
        "s"
        [("s", [leaf "zero", leaf "one", FTA.Transition (sym "add") ["s", "s"] equal, node "multiply" ["s", "s"]])]
  where
    equal = equalityConstraint $ ECTA.mkEqConstraints [[ECTA.path [0], ECTA.path [1]]]

{- | A walk on every prefix of every accepted term, and every such prefix with
one more token: the step is 'Nothing' exactly where 'afterPrefix' of the listed
completions is, and the walk offers the tokens of 'nextTokens'.
-}
walksAsListing ::
    (Ord state) =>
    (Entailment -> Size -> FTA.FTA state Symbol Constraint -> IO Deciding) ->
    Integer ->
    FTA.FTA state Symbol Constraint ->
    IO ()
walksAsListing walking bound graph = do
    let eager = start bound graph
        tokens =
            nubOrd
                [ (FTA.transitionSymbol transition, length $ FTA.transitionChildren transition)
                | transition <- concat $ Map.elems $ FTA.transitionTable graph
                ]
        prefixes = nubOrd $ concat [inits tokens' | term <- completionTerms eager, tokens' <- [preorder term]]
    walk <- walking unusedSolver (Size bound) graph
    forM_ (prefixes <> [prefix <> [token] | prefix <- prefixes, token <- tokens]) $ \prefix -> do
        walked <- walkTo walk prefix
        let expected = afterPrefix eager prefix
        (prefix, isJust walked) `shouldBe` (prefix, isJust expected)
        case (walked, expected) of
            (Just found, Just after) -> do
                verdicts <- decidingTokens found
                (prefix, verdicts)
                    `shouldBe` (prefix, (if isComplete after then Yes else No, [(token, Yes) | (token, _) <- nextTokens after]))
            _ -> pure ()

-- | A walk after the tokens of a prefix, the first token first.
walkTo :: Deciding -> [(Symbol, Int)] -> IO (Maybe Deciding)
walkTo walk [] = pure (Just walk)
walkTo walk (token : rest) = decidingStep walk token >>= maybe (pure Nothing) (`walkTo` rest)

-- | A solver that fails the test when the walk calls it.
unusedSolver :: Entailment
unusedSolver = Entailment $ \_ _ -> fail "unexpected solver call"

{- | A recursion in which @f(a)@ and @f(f(a))@ have two runs.
| A symbol with one child and with two children, and a leaf.
-}
mixedArities :: FTA.FTA String Symbol Constraint
mixedArities = automaton "s" [("s", [leaf "a", node "f" ["s"], node "f" ["s", "s"]])]

{- | A symbol with three children, a symbol with one child, and two leaves.
The size index orders the sizes of the three children of a term with six
nodes as (1,1,3), (1,2,2), (2,1,2), (1,3,1), (2,2,1), (3,1,1), not in
lexicographic order.
-}
threeChildren :: FTA.FTA String Symbol Constraint
threeChildren = automaton "s" [("s", [leaf "a", leaf "b", node "f" ["s"], node "h" ["s", "s", "s"]])]

overlapping :: FTA.FTA String Symbol Constraint
overlapping =
    automaton
        "s"
        [ ("s", [leaf "a", node "f" ["p"], node "f" ["q"], node "g" ["s", "s"]])
        , ("p", [leaf "a", leaf "b", node "f" ["p"]])
        , ("q", [leaf "a", node "f" ["q"]])
        ]

-- | An automaton from rows of named states.
automaton :: String -> [(String, [FTA.Transition String Symbol Constraint])] -> FTA.FTA String Symbol Constraint
automaton initial rows = either (error . show) id $ FTA.mkFTA initial rows

-- | A transition without children.
leaf :: String -> FTA.Transition String Symbol Constraint
leaf symbol = FTA.Transition (sym symbol) [] noConstraint

-- | A transition without a constraint.
node :: String -> [String] -> FTA.Transition String Symbol Constraint
node symbol children = FTA.Transition (sym symbol) children noConstraint

-- | A symbol from its name.
sym :: String -> Symbol
sym = Symbol . Text.pack
