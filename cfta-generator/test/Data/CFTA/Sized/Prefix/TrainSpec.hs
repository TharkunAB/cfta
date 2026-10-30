module Data.CFTA.Sized.Prefix.TrainSpec (spec) where

import Control.Monad (forM_)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalityConstraint, noConstraint)
import qualified Data.CFTA.Equality as ECTA
import Data.CFTA.Sized.Prefix (Completions, afterToken, completionTerms, prefixCompletions)
import Data.CFTA.Sized.Prefix.QuickCheck (sampleWeighted)
import Data.CFTA.Sized.Prefix.Train
import Data.CFTA.Term (Term)
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

-- | A small corpus of completions within the bound 9.
corpus :: [Term String]
corpus = take 40 $ cycle $ take 10 $ drop 3 $ completionTerms $ completionsOf 9 expressions
