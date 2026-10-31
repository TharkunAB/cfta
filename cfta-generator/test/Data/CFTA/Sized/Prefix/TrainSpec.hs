module Data.CFTA.Sized.Prefix.TrainSpec (spec) where

import Control.Monad (forM_)
import Data.Containers.ListUtils (nubOrd)
import Data.List (inits, isPrefixOf, sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isNothing)
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalityConstraint, noConstraint)
import qualified Data.CFTA.Equality as ECTA
import Data.CFTA.Sized.Prefix (Completions, Token, afterToken, completionTerms, prefixCompletions)
import qualified Data.CFTA.Sized.Prefix.Model as Model
import Data.CFTA.Sized.Prefix.Parents (Reach (..))
import Data.CFTA.Sized.Prefix.QuickCheck (sampleWeighted)
import Data.CFTA.Sized.Prefix.Train
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Gen as QCGen
import qualified Test.QuickCheck.Random as QCRandom

spec :: Spec
spec = describe "Data.CFTA.Sized.Prefix.Train" $ do
    it "gives the expected counts of brute force, exactly, from the count table and from a listing" $
        forM_ [expressions, doubles] $ \automaton -> do
            let completions = completionsOf 6 automaton
                terms = completionTerms completions
                weightOfTerm term = product $ map exactWeight $ foldr (:) [] term
                total = sum $ map weightOfTerm terms
                brute =
                    Map.map (/ total) $
                        Map.fromListWith (+) [(symbol, weightOfTerm term) | term <- terms, symbol <- foldr (:) [] term]
            expectedCounts exactWeight completions `shouldBe` (total, brute)
    it "gives the gradient of the log-likelihood, as finite differences do, orthogonal to the arity direction" $ do
        let completions = completionsOf 9 expressions
            counts = meanCounts corpus
            point = Map.fromList [("x", 0.3), ("y", -0.2), ("neg", -1.1), ("add", -0.7)]
            (_, gradient) = logLikelihood (completionsOracle completions) counts point
            at shift = fst $ logLikelihood (completionsOracle completions) counts $ Map.unionWith (+) point shift
            step = 1e-5
        forM_ (Map.toList gradient) $ \(symbol, slope) -> do
            let difference = (at (Map.singleton symbol step) - at (Map.singleton symbol (negate step))) / (2 * step)
            abs (difference - slope) `shouldSatisfy` (< 1e-6)
        abs (sum [arityLess symbol * slope | (symbol, slope) <- Map.toList gradient]) `shouldSatisfy` (< 1e-9)
    it "gives the expected counts of the dual numbers by inside-outside on the automaton" $ do
        let point = Map.fromList [("x", 0.3), ("y", -0.2), ("neg", -1.1), ("add", -0.7)]
            (dualLog, dualCounts) = oracleExpectations (completionsOracle $ completionsOf 9 expressions) point
            (insideLog, insideCounts) = oracleExpectations (automatonOracle expressions 9) point
        abs (dualLog - insideLog) `shouldSatisfy` (< 1e-9)
        Map.keys insideCounts `shouldBe` Map.keys dualCounts
        forM_ (Map.toList dualCounts) $ \(symbol, count) ->
            abs (count - insideCounts Map.! symbol) `shouldSatisfy` (< 1e-9)
    it "gives the expected counts of brute force with equal children, by inside-outside on the intersections" $
        forM_ [doubles, towers] $ \automaton -> do
            let point = Map.fromList [("x", 0.3), ("y", -0.2), ("neg", -1.1), ("add", -0.7), ("f", -0.4)]
                terms = completionTerms $ completionsOf 9 automaton
                weightOfTerm term = exp $ sum [Map.findWithDefault 0 symbol point | symbol <- foldr (:) [] term]
                total = sum $ map weightOfTerm terms
                brute =
                    Map.map (/ total) $
                        Map.fromListWith (+) [(symbol, weightOfTerm term) | term <- terms, symbol <- foldr (:) [] term]
                oracle = fromJust $ constrainedOracle automaton 9
                (logTotal, counts) = oracleExpectations oracle point
            abs (logTotal - log total) `shouldSatisfy` (< 1e-9)
            Map.keys counts `shouldBe` Map.keys brute
            forM_ (Map.toList brute) $ \(symbol, count) ->
                abs (count - counts Map.! symbol) `shouldSatisfy` (< 1e-9)
    it "distills a teacher from its samples, on the plain, the deterministic, and the intersection route" $
        forM_ [expressions, ambiguousExpressions, doubles] $ \automaton -> do
            let completions = completionsOf 7 automaton
                -- Weights that are powers of two keep the draws short.
                teacher = Map.fromList [("x", log 2), ("y", log 0.5), ("neg", log 0.25), ("add", log 0.5)]
                generator = fromJust $ sampleWeighted (fromJust $ withLogWeights teacher completions)
                samples = QCGen.unGen (QC.vectorOf 2000 generator) (QCRandom.mkQCGen 7) 30
                fitted = fromJust $ distill automaton 7 samples
                report = either (error . show) id $ distillWithReport automaton 7 samples
            stepWeights (fitFinalStep $ distillFit report) `shouldBe` fitted
            (distillRetained report, distillDropped report) `shouldBe` (2000, 0)
            forM_ [[], [("add", 2)], [("neg", 1)]] $ \prefix -> do
                let after = foldl (\current token -> fromJust $ afterToken current token) completions prefix
                forM_ (zip (nextTokenDistribution teacher after) (nextTokenDistribution fitted after)) $
                    \((token, expected), (_, found)) ->
                        (token, abs (found - expected) < 0.05) `shouldBe` (token, True)
    it "recovers the distribution of a teacher from its expected counts, up to the arity direction" $ do
        let completions = completionsOf 9 expressions
            teacher = Map.fromList [("x", 0.5), ("y", -0.5), ("neg", -1.5), ("add", -1)]
            counts = snd $ expectedCounts (exp . (teacher Map.!)) completions
            steps = take 2000 $ fit 0 (completionsOracle completions) counts Map.empty
            fitted = stepWeights $ last steps
            prefixes = [[], [("add", 2)], [("add", 2), ("x", 0)], [("neg", 1)]]
        stepGradientNorm (last steps) `shouldSatisfy` (< 1e-8)
        forM_ prefixes $ \prefix -> do
            let after = foldl (\current token -> fromJust $ afterToken current token) completions prefix
            forM_ (zip (nextTokenDistribution teacher after) (nextTokenDistribution fitted after)) $
                \((token, expected), (fittedToken, found)) -> do
                    fittedToken `shouldBe` token
                    abs (found - expected) `shouldSatisfy` (< 1e-6)
        -- The difference of the log-weights is a multiple of (arity - 1).
        let difference symbol = Map.findWithDefault 0 symbol fitted - teacher Map.! symbol
            scale = difference "add"
        forM_ ["x", "y", "neg", "add"] $ \symbol ->
            abs (difference symbol - scale * arityLess symbol) `shouldSatisfy` (< 1e-5)

    describe "training reports" $ do
        it "reports the retained corpus and preserves the default fit" $ do
            let retained = [Term.Node "x" [], Term.Node "y" []]
                terms = retained <> [Term.Node "neg" [Term.Node "x" []], Term.Node "outside" []]
                report = either (error . show) id $ distillWithReport expressions 1 terms
            (distillRetained report, distillDropped report) `shouldBe` (2, 2)
            Just (stepWeights $ fitFinalStep $ distillFit report) `shouldBe` distill expressions 1 retained
        it "distinguishes an empty retained corpus from an unsupported training language" $ do
            fmap distillRetained (distillWithReport expressions 1 []) `shouldBe` Left NoRetainedTerms
            fmap distillRetained (distillWithReport expressions 1 [Term.Node "outside" []]) `shouldBe` Left NoRetainedTerms
            let deep = equalityConstraint $ ECTA.mkEqConstraints [[ECTA.path [0, 0], ECTA.path [1, 0]]]
                unsupported = FTA.mapConstraints (const deep) expressions
            fmap distillRetained (distillWithReport unsupported 5 corpus) `shouldBe` Left UnsupportedTrainingLanguage
        it "does not start a line search after the step budget is spent" $ do
            let oracle = Oracle ["x"] (error "the step limit must not evaluate trial points") (const (0, Map.empty))
                report = either (error . show) id $ fitWithReport 1 0 oracle (Map.singleton "x" 1) Map.empty
            (fitStepCount report, fitStopReason report) `shouldBe` (1, StepLimit)
            stepGradientNorm (fitFinalStep report) `shouldBe` 1
            length (take 1 $ fit 0 oracle (Map.singleton "x" 1) Map.empty) `shouldBe` 1
        it "reports a known gradient stop at the step limit" $ do
            let oracle = Oracle ["x"] (error "a stationary point needs no line search") (const (0, Map.singleton "x" 1))
                report = either (error . show) id $ fitWithReport 1 0 oracle (Map.singleton "x" 1) Map.empty
            (fitStepCount report, fitStopReason report) `shouldBe` (1, GradientTolerance)
        it "reports a small objective change without calling it a gradient stop" $ do
            let report = either (error . show) id $ fitWithReport 2 0 (bernoulliOracle 1e12) (Map.singleton "x" 0.8) Map.empty
            (fitStepCount report, fitStopReason report) `shouldBe` (2, ObjectiveTolerance)
            stepGradientNorm (fitFinalStep report) `shouldSatisfy` (> 1e-3)
        it "reports a failed line search without adding a step" $ do
            let oracle = Oracle ["x"] (const 2) (const (0, Map.empty))
                report = either (error . show) id $ fitWithReport 2 0 oracle (Map.singleton "x" 1) Map.empty
            (fitStepCount report, fitStopReason report) `shouldBe` (1, LineSearchFailed)
            stepWeights (fitFinalStep report) `shouldBe` Map.singleton "x" 0
        it "preserves every bounded prefix of the legacy fit" $ do
            let oracle = bernoulliOracle 0
                counts = Map.singleton "x" 0.75
                legacy = fit 0 oracle counts Map.empty
            forM_ [1, 2, 3, 100] $ \limit -> do
                let expected = take limit legacy
                    report = either (error . show) id $ fitWithReport limit 0 oracle counts Map.empty
                    actual = fitFinalStep report
                fitStepCount report `shouldBe` length expected
                stepWeights actual `shouldBe` stepWeights (last expected)
                stepObjective actual `shouldBe` stepObjective (last expected)
                stepGradientNorm actual `shouldBe` stepGradientNorm (last expected)
            abs (Map.findWithDefault 0 "x" (stepWeights $ last legacy) - log 3) `shouldSatisfy` (< 1e-6)
        it "rejects invalid reporting inputs before evaluating the oracle" $ do
            let oracle = error "invalid inputs must not evaluate the oracle" :: Oracle String
                report limit precision counts start = fmap fitStepCount $ fitWithReport limit precision oracle counts start
            forM_ [0, -1] $ \limit -> report limit 0 Map.empty Map.empty `shouldBe` Left InvalidStepLimit
            forM_ [-1, 0 / 0, 1 / 0] $ \precision -> report 1 precision Map.empty Map.empty `shouldBe` Left InvalidPrecision
            forM_ [-1, 0 / 0, 1 / 0] $ \count -> report 1 0 (Map.singleton "x" count) Map.empty `shouldBe` Left InvalidCounts
            forM_ [0 / 0, 1 / 0] $ \weight -> report 1 0 Map.empty (Map.singleton "x" weight) `shouldBe` Left InvalidInitialWeights
        it "rejects non-finite steps instead of returning a successful report" $
            forM_ [(0 / 0, Map.empty), (1 / 0, Map.empty), (0, Map.singleton "x" (1 / 0))] $ \result -> do
                let oracle = Oracle ["x"] (error "a non-finite step must stop before the line search") (const result)
                fmap fitStepCount (fitWithReport 2 0 oracle Map.empty Map.empty) `shouldBe` Left NonFiniteStep

    describe "Model" $ do
        let models =
                [ (reach, fromJust $ Model.train reach expressions 5 corpus)
                | reach <- [Reach 0 False, Reach 1 False, Reach 2 True]
                ]
            everything model = fromJust $ Model.bestTerms 100000 model []
            close left right = abs (left - right) < 1e-7
        it "returns the same model queries with an inspectable training report" $
            forM_ models $ \(reach, model) -> do
                let (reported, report) = either (error . show) id $ Model.trainWithReport reach expressions 5 corpus
                everything reported `shouldBe` everything model
                Model.nextTokenProbabilities reported [] `shouldBe` Model.nextTokenProbabilities model []
                (distillRetained report, distillDropped report) `shouldBe` (length corpus, 0)
                fitStepCount (distillFit report) `shouldSatisfy` (\count -> count > 0 && count <= 2000)
        it "reports dropped terms without requiring callers to label the corpus" $ do
            let terms = [Term.Node "x" [], Term.Node "y" [], Term.Node "neg" [Term.Node "x" []], Term.Node "outside" []]
                (model, report) = either (error . show) id $ Model.trainWithReport (Reach 1 True) expressions 1 terms
            (distillRetained report, distillDropped report) `shouldBe` (2, 2)
            Map.fromList (everything model) `shouldBe` Map.fromList [(Term.Node "x" [], 0.5), (Term.Node "y" [], 0.5)]
        it "reports an empty retained corpus or unsupported context labelling" $ do
            let outcome automaton terms = fmap (distillRetained . snd) $ Model.trainWithReport (Reach 1 True) automaton 5 terms
            outcome expressions [] `shouldBe` Left NoRetainedTerms
            outcome expressions [Term.Node "outside" []] `shouldBe` Left NoRetainedTerms
            outcome doubles corpus `shouldBe` Left UnsupportedTrainingLanguage
        it "gives each term within the bound a probability, the probabilities sum to one, and the most probable come first" $
            forM_ models $ \(reach, model) -> do
                let best = everything model
                (reach, sort $ map fst best) `shouldBe` (reach, sort $ completionTerms $ completionsOf 5 expressions)
                (reach, close (sum $ map snd best) 1) `shouldBe` (reach, True)
                (reach, and $ zipWith (>=) (map snd best) (drop 1 $ map snd best)) `shouldBe` (reach, True)
                forM_ best $ \(term, probability) ->
                    (reach, term, close (log probability) <$> Model.termLogProbability model term) `shouldBe` (reach, term, Just True)
        it "gives each next token the probability of its completions" $
            forM_ models $ \(reach, model) -> do
                let best = everything model
                forM_ (nubOrd $ concatMap (inits . preorder . fst) best) $ \prefix -> do
                    let within = [(preorder term, probability) | (term, probability) <- best, prefix `isPrefixOf` preorder term]
                        total = sum $ map snd within
                        expected =
                            Map.toList $
                                Map.fromListWith
                                    (+)
                                    [(tokens !! length prefix, probability / total) | (tokens, probability) <- within, length tokens > length prefix]
                        found = fromJust $ Model.nextTokenProbabilities model prefix
                    (reach, prefix, map fst found) `shouldBe` (reach, prefix, map fst expected)
                    (reach, prefix, and $ zipWith close (map snd found) (map snd expected)) `shouldBe` (reach, prefix, True)
        it "raises the probabilities of the terms to one over the temperature" $
            forM_ models $ \(reach, model) -> do
                let best = everything model
                    cooled = Map.fromList $ everything $ fromJust $ Model.withTemperature 0.5 model
                    total = sum [probability ^ (2 :: Int) | (_, probability) <- best]
                forM_ best $ \(term, probability) ->
                    (reach, term, close (cooled Map.! term) (probability ^ (2 :: Int) / total)) `shouldBe` (reach, term, True)
                (reach, isNothing $ Model.withTemperature 0 model) `shouldBe` (reach, True)
        it "samples completions of the prefix, and no completion of a prefix outside the language" $
            forM_ models $ \(reach, model) -> do
                forM_ [[], [("add", 2)], [("add", 2), ("neg", 1)]] $ \prefix -> do
                    let drawn = QCGen.unGen (QC.vectorOf 50 $ fromJust $ Model.sampleTerm model prefix) (QCRandom.mkQCGen 3) 30
                    (reach, prefix, filter (not . isPrefixOf prefix . preorder) drawn) `shouldBe` (reach, prefix, [])
                (reach, isNothing $ Model.sampleTerm model [("x", 0), ("y", 0)]) `shouldBe` (reach, True)

-- | The log partition and expected count of one Bernoulli feature, with a constant offset.
bernoulliOracle :: Double -> Oracle String
bernoulliOracle offset = Oracle ["x"] partition expectations
  where
    weight point = exp $ Map.findWithDefault 0 "x" point
    partition point = offset + log (1 + weight point)
    expectations point = (partition point, Map.singleton "x" (weight point / (1 + weight point)))

-- | Expressions: x, y, neg(e), add(e, e).
expressions :: FTA.FTA String String Constraint
expressions =
    either (error . show) id $
        FTA.mkFTA "e" [("e", [node "x" [], node "y" [], node "neg" ["e"], node "add" ["e", "e"]])]
  where
    node symbol children = FTA.Transition symbol children noConstraint

-- | Expressions with equal children, which the completions list.
doubles :: FTA.FTA String String Constraint
doubles =
    either (error . show) id $
        FTA.mkFTA "e" [("e", [node "x" [], node "y" [], node "neg" ["e"], FTA.Transition "add" ["e", "e"] equal])]
  where
    node symbol children = FTA.Transition symbol children noConstraint
    equal = equalityConstraint $ ECTA.mkEqConstraints [[ECTA.path [0], ECTA.path [1]]]

-- | Expressions with a second, overlapping definition of add: ambiguous rows.
ambiguousExpressions :: FTA.FTA String String Constraint
ambiguousExpressions =
    either (error . show) id $
        FTA.mkFTA
            "e"
            [ ("e", [node "x" [], node "y" [], node "neg" ["e"], node "add" ["e", "e"], node "add" ["v", "e"]])
            , ("v", [node "x" [], node "y" []])
            ]
  where
    node symbol children = FTA.Transition symbol children noConstraint

-- | Pairs of equal children from two different states: their intersection holds the towers of even height.
towers :: FTA.FTA String String Constraint
towers =
    either (error . show) id $
        FTA.mkFTA
            "s"
            [ ("s", [FTA.Transition "add" ["a", "c"] equal, node "neg" ["s"]])
            , ("a", [node "x" [], node "f" ["a"]])
            , ("c", [node "x" [], node "f" ["d"]])
            , ("d", [node "f" ["c"]])
            ]
  where
    node symbol children = FTA.Transition symbol children noConstraint
    equal = equalityConstraint $ ECTA.mkEqConstraints [[ECTA.path [0], ECTA.path [1]]]

completionsOf :: Integer -> FTA.FTA String String Constraint -> Completions String
completionsOf bound = either (error . show) id . prefixCompletions (fromInteger bound)

-- | Weights with distinct values, so a wrong count shows.
exactWeight :: String -> Rational
exactWeight symbol = case symbol of
    "x" -> 1
    "y" -> 2
    "neg" -> 1 / 3
    _ -> 1 / 2

-- | The arity of a symbol minus one: the direction of the log-weights that does not change the distribution.
arityLess :: String -> Double
arityLess symbol = case symbol of
    "neg" -> 0
    "add" -> 1
    _ -> -1

-- | The tokens of a term in preorder.
preorder :: Term String -> [Token String]
preorder (Term.Node symbol children) = (symbol, length children) : concatMap preorder children

-- | A small corpus of completions within the bound 9.
corpus :: [Term String]
corpus = take 40 $ cycle $ take 10 $ drop 3 $ completionTerms $ completionsOf 9 expressions
