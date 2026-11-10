module Data.CFTA.Sized.Prefix.TrainSpec (spec) where

import Control.Monad (forM_)
import Data.Containers.ListUtils (nubOrd)
import Data.List (inits, isPrefixOf, sort, sortOn)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe, isNothing)
import Data.Ord (Down (..))
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalityConstraint, noConstraint)
import qualified Data.CFTA.Equality as ECTA
import Data.CFTA.Ranked.Internal.Sampler (Exact (..))
import Data.CFTA.Sized.Prefix (
    Completions,
    Token,
    afterToken,
    completionTerms,
    completionWeight,
    prefixCompletions,
    withWeights,
 )
import qualified Data.CFTA.Sized.Prefix.Mixture as Mixture
import qualified Data.CFTA.Sized.Prefix.Model as Model
import Data.CFTA.Sized.Prefix.Parents (Reach (..))
import Data.CFTA.Sized.Prefix.QuickCheck (sampleWeighted)
import Data.CFTA.Sized.Prefix.Train
import Data.CFTA.Template (Exclusion (..), Template (..), excludeAllFTA, restrictFTA)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Gen as QCGen
import qualified Test.QuickCheck.Random as QCRandom

spec :: Spec
spec = describe "Data.CFTA.Sized.Prefix.Train" $ do
    it "rejects invalid exponential weights before they can become zero rational weights" $ do
        let completions = completionsOf 1 expressions
        forM_ [0 / 0, 1 / 0, -1 / 0, 1000, -1000] $ \weight ->
            isNothing (withLogWeights (Map.singleton "x" weight) completions) `shouldBe` True
        completionWeight <$> withLogWeights (Map.singleton "x" (log 2)) completions `shouldBe` Just 3
        completionWeight <$> withWeights (\symbol -> if symbol == "x" then 0 else 1) completions `shouldBe` Just 1
    it "keeps default weights and ignores unused log-weight entries" $ do
        let completions = completionsOf 1 expressions
        completionWeight <$> withLogWeights Map.empty completions `shouldBe` Just 2
        completionWeight <$> withLogWeights (Map.singleton "unused" (0 / 0)) completions `shouldBe` Just 2
    it "keeps a finite positive exponential when its approximation endpoint would overflow" $ do
        let singleton = FTA.fromTerms [Term.Node "x" []]
            completions = either (error . show) id $ prefixCompletions 1 singleton
            weight = log (encodeFloat (2 ^ (53 :: Int) - 1) (1024 - 53) :: Double)
            value = exp weight
        value `shouldSatisfy` (\x -> x > 0 && not (isInfinite x))
        value + value * 1e-9 `shouldSatisfy` isInfinite
        completionWeight <$> withLogWeights (Map.singleton "x" weight) completions `shouldBe` Just (toRational value)
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
    it "fits a mixture of one group to the log-weights of distill" $ do
        let fitted = fromJust $ distillMixture expressions 9 [[], corpus, [Term.Node "outside" []]]
            direct = fromJust $ distill expressions 9 corpus
            deep = equalityConstraint $ ECTA.mkEqConstraints [[ECTA.path [0, 0], ECTA.path [1, 0]]]
        map fst fitted `shouldBe` [1]
        forM_ (Map.toList direct) $ \(symbol, weight) ->
            (symbol, [abs (found Map.! symbol - weight) < 1e-6 | (_, found) <- fitted]) `shouldBe` (symbol, [True])
        isNothing (distillMixture expressions 1 [[], [Term.Node "outside" []]]) `shouldBe` True
        isNothing (distillMixture (FTA.mapConstraints (const deep) expressions) 5 [corpus]) `shouldBe` True

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
            -- Whether two lists of terms with probabilities have the same terms, each with a close probability.
            closeTerms left right =
                let (first, second) = (Map.fromList left, Map.fromList right)
                 in Map.keys first == Map.keys second && and (Map.intersectionWith close first second)
            -- The prefixes of the terms within the bound.
            prefixes = nubOrd $ concatMap (inits . preorder) $ completionTerms $ completionsOf 5 expressions
            -- Each model with the name of an event, the event, the model given the event, and the probability of
            -- the event after each prefix.
            given =
                [ ( reach
                  , name
                  , event
                  , model
                  , conditioned
                  , Map.fromList [(prefix, Model.eventProbability conditioned prefix) | prefix <- prefixes]
                  )
                | (reach, model) <- models
                , (name, event) <- [("without y", withoutY), ("root add", rootAdd)]
                , let conditioned = fromJust $ Model.condition event model
                ]
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
        it "gives each next token its probability when the weight of the prefix is outside the range of Double" $
            forM_ models $ \(reach, model) -> do
                -- At this temperature, the weight of some prefixes is outside the range of Double.
                let cold = fromJust $ Model.withTemperature 0.007 model
                forM_ (nubOrd $ concatMap (inits . preorder . fst) $ everything model) $ \prefix -> do
                    let expected =
                            Map.toList $
                                Map.fromListWith
                                    (+)
                                    [ (tokens !! length prefix, probability)
                                    | (term, probability) <- fromJust $ Model.bestTerms 100000 cold prefix
                                    , let tokens = preorder term
                                    , length tokens > length prefix
                                    ]
                        found = fromJust $ Model.nextTokenProbabilities cold prefix
                    (reach, prefix, map fst found) `shouldBe` (reach, prefix, map fst expected)
                    (reach, prefix, and $ zipWith close (map snd found) (map snd expected)) `shouldBe` (reach, prefix, True)
        it "raises the probabilities of the terms to one over the temperature" $
            forM_ models $ \(reach, model) -> do
                let best = everything model
                    cooled = Map.fromList $ everything $ fromJust $ Model.withTemperature 0.5 model
                    total = sum [probability ^ (2 :: Int) | (_, probability) <- best]
                forM_ best $ \(term, probability) ->
                    (reach, term, close (cooled Map.! term) (probability ^ (2 :: Int) / total)) `shouldBe` (reach, term, True)
                forM_ [0, -1, 0 / 0, 1 / 0, -1 / 0] $ \temperature ->
                    (reach, isNothing $ Model.withTemperature temperature model) `shouldBe` (reach, True)
                let restored = fromJust $ Model.withTemperature 1 $ fromJust $ Model.withTemperature 0.5 model
                everything restored `shouldBe` best
        it "samples completions of the prefix, and no completion of a prefix outside the language" $
            forM_ models $ \(reach, model) -> do
                forM_ [[], [("add", 2)], [("add", 2), ("neg", 1)]] $ \prefix -> do
                    let drawn = QCGen.unGen (QC.vectorOf 50 $ fromJust $ Model.sampleTerm model prefix) (QCRandom.mkQCGen 3) 30
                    (reach, prefix, filter (not . isPrefixOf prefix . preorder) drawn) `shouldBe` (reach, prefix, [])
                (reach, isNothing $ Model.sampleTerm model [("x", 0), ("y", 0)]) `shouldBe` (reach, True)
        it "keeps each probability given an event that each term is in" $
            forM_ models $ \(reach, model) -> do
                let conditioned = fromJust $ Model.condition expressions model
                (reach, closeTerms (everything conditioned) (everything model)) `shouldBe` (reach, True)
                forM_ prefixes $ \prefix -> do
                    (reach, prefix, Model.eventProbability model prefix) `shouldBe` (reach, prefix, Just 1)
                    (reach, prefix, close 1 <$> Model.eventProbability conditioned prefix) `shouldBe` (reach, prefix, Just True)
                    let found = fromJust $ Model.nextTokenProbabilities conditioned prefix
                        expected = fromJust $ Model.nextTokenProbabilities model prefix
                    (reach, prefix, map fst found) `shouldBe` (reach, prefix, map fst expected)
                    (reach, prefix, and $ zipWith close (map snd found) (map snd expected)) `shouldBe` (reach, prefix, True)
        it "gives each term of an event its probability over the probability of the event, and no other term a probability" $
            forM_ given $ \(reach, name, event, model, conditioned, _) -> do
                let best = everything model
                    total = sum [probability | (term, probability) <- best, FTA.accepts event term]
                (reach, name, close (sum $ map snd $ everything conditioned) 1) `shouldBe` (reach, name, True)
                forM_ best $ \(term, probability) ->
                    (reach, name, term, close (log $ probability / total) <$> Model.termLogProbability conditioned term)
                        `shouldBe` (reach, name, term, if FTA.accepts event term then Just True else Nothing)
        it "gives the probability of an event after each prefix, as the sums over the terms give it" $
            forM_ given $ \(reach, name, event, model, conditioned, after) -> do
                let flagged = [(preorder term, probability, FTA.accepts event term) | (term, probability) <- everything model]
                forM_ prefixes $ \prefix -> do
                    let within = [(probability, accepted) | (tokens, probability, accepted) <- flagged, prefix `isPrefixOf` tokens]
                        inEvent = sum [probability | (probability, True) <- within]
                    if inEvent == 0
                        then (reach, name, prefix, after Map.! prefix) `shouldBe` (reach, name, prefix, Just 0)
                        else
                            (reach, name, prefix, close (inEvent / sum (map fst within)) <$> after Map.! prefix)
                                `shouldBe` (reach, name, prefix, Just True)
                forM_ [[("x", 0), ("y", 0)], [("neg", 2)]] $ \prefix ->
                    (reach, name, prefix, Model.eventProbability conditioned prefix) `shouldBe` (reach, name, prefix, Nothing)
        it "gives the next-token probabilities of the lookahead: P(x | p, E) P(E | p) = P(x | p) P(E | p <> [x])" $
            forM_ given $ \(reach, name, _, model, conditioned, after) -> do
                let probabilityAfter prefix = fromJust $ after Map.! prefix
                forM_ prefixes $ \prefix -> do
                    let lookahead = fromMaybe [] $ Model.nextTokenProbabilities conditioned prefix
                    forM_ (fromJust $ Model.nextTokenProbabilities model prefix) $ \(token, probability) ->
                        ( reach
                        , name
                        , prefix
                        , token
                        , close
                            (fromMaybe 0 (lookup token lookahead) * probabilityAfter prefix)
                            (probability * probabilityAfter (prefix <> [token]))
                        )
                            `shouldBe` (reach, name, prefix, token, True)
        it "gives the same model when it conditions at a temperature and when it sets the temperature after" $
            forM_ given $ \(reach, name, event, model, conditioned, _) -> do
                let first = fromJust $ Model.condition event $ fromJust $ Model.withTemperature 0.5 model
                    second = fromJust $ Model.withTemperature 0.5 conditioned
                (reach, name, everything first) `shouldBe` (reach, name, everything second)
                (reach, name, Model.nextTokenProbabilities first []) `shouldBe` (reach, name, Model.nextTokenProbabilities second [])
                -- The prefixes with at most two tokens, to keep the law fast.
                forM_ (filter ((<= 2) . length) prefixes) $ \prefix ->
                    (reach, name, prefix, Model.eventProbability first prefix)
                        `shouldBe` (reach, name, prefix, Model.eventProbability second prefix)
        it "gives the model given both events when it conditions twice" $
            forM_ models $ \(reach, model) -> do
                let twice = fromJust $ Model.condition rootAdd =<< Model.condition withoutY model
                    both =
                        FTA.intersectWith (\left right -> if left == right then Just left else Nothing) (\_ _ -> noConstraint) withoutY rootAdd
                    once = fromJust $ Model.condition both model
                (reach, closeTerms (everything twice) (everything once)) `shouldBe` (reach, True)
                forM_ prefixes $ \prefix ->
                    (reach, prefix, close <$> Model.eventProbability twice prefix <*> Model.eventProbability once prefix)
                        `shouldBe` (reach, prefix, Just True)
        it "conditions on the restriction to a template, or to the terms that no exclusion rejects, as on the same event" $
            forM_ models $ \(reach, model) -> do
                let restricted =
                        [ ("without y", withoutY, Model.condition (excludeAllFTA [Anywhere (TemplateNode "y" [])] expressions) model)
                        , ("root add", rootAdd, Model.condition (restrictFTA (TemplateNode "add" [Hole, Hole]) expressions) model)
                        ]
                forM_ restricted $ \(name, event, conditioned) ->
                    (reach, name, closeTerms (everything $ fromJust $ Model.condition event model) . everything <$> conditioned)
                        `shouldBe` (reach, name, Just True)
        it "gives no model for an event with a constraint or without a term in the bound, and draws only terms of the event" $ do
            forM_ models $ \(reach, model) -> do
                (reach, isNothing $ Model.condition doubles model) `shouldBe` (reach, True)
                -- A term with six nodes, beyond the bound.
                let deep = iterate (\term -> Term.Node "neg" [term]) (Term.Node "x" []) !! 5
                (reach, isNothing $ Model.condition (FTA.fromTerms [deep]) model) `shouldBe` (reach, True)
            forM_ given $ \(reach, name, event, _, conditioned, _) -> do
                let drawn = QCGen.unGen (QC.vectorOf 50 $ fromJust $ Model.sampleTerm conditioned []) (QCRandom.mkQCGen 3) 30
                (reach, name, filter (not . FTA.accepts event) drawn) `shouldBe` (reach, name, [])

    describe "Mixture" $ do
        let reaches = [Reach 0 False, Reach 1 False, Reach 2 True]
            terms = completionTerms $ completionsOf 5 expressions
            prefixes = nubOrd $ concatMap (inits . preorder) terms
            probability mixture = exp . fromJust . Mixture.termLogProbability mixture
            close left right = abs (left - right) < 1e-7
            -- The terms whose leaves are all the given variable.
            only variable = [term | term <- terms, and [symbol == variable | (symbol, 0) <- preorder term]]
            -- The fit of two components is slow with the largest reach, so the laws of two components use the first two.
            mixtures = [(reach, fromJust $ Mixture.train reach expressions 5 [only "x", only "y"]) | reach <- take 2 reaches]
            negated left right = Term.Node "add" [Term.Node "neg" [Term.Node left []], Term.Node "neg" [Term.Node right []]]
            -- The exact mass of each term in the draws of a mixture.
            masses mixture = Map.fromListWith (+) [(term, mass) | (mass, term) <- runExact $ fromJust $ Mixture.lowerTerm mixture []]
            events = [("without y", withoutY), ("root add", rootAdd)]
            -- Each mixture of two components with the name of an event, the event, and the mixture given the event.
            given =
                [ (reach, name, event, mixture, fromJust $ Mixture.condition event mixture)
                | (reach, mixture) <- mixtures
                , (name, event) <- events
                ]
        it "is the model when the corpus has one group" $
            forM_ reaches $ \reach -> do
                let mixture = fromJust $ Mixture.train reach expressions 5 [corpus]
                    model = fromJust $ Model.train reach expressions 5 corpus
                (reach, Mixture.componentProbabilities mixture []) `shouldBe` (reach, Just [1])
                forM_ terms $ \term ->
                    (reach, term, close (probability mixture term) . exp <$> Model.termLogProbability model term)
                        `shouldBe` (reach, term, Just True)
                forM_ prefixes $ \prefix -> do
                    let found = fromJust $ Mixture.nextTokenProbabilities mixture prefix
                        expected = fromJust $ Model.nextTokenProbabilities model prefix
                    (reach, prefix, map fst found) `shouldBe` (reach, prefix, map fst expected)
                    (reach, prefix, and $ zipWith close (map snd found) (map snd expected)) `shouldBe` (reach, prefix, True)
                    let every = Map.fromList $ fromJust $ Mixture.bestTerms 100000 mixture prefix
                        expectedEvery = Map.fromList $ fromJust $ Model.bestTerms 100000 model prefix
                    (reach, prefix, Map.keys every, and $ Map.intersectionWith close every expectedEvery)
                        `shouldBe` (reach, prefix, Map.keys expectedEvery, True)
                -- The model can give the completions with equal probabilities in another order.
                forM_ [1, 2, 5] $ \count -> do
                    let best = fromJust $ Mixture.bestTerms count mixture []
                        expectedBest = fromJust $ Model.bestTerms count model []
                    (reach, count, length best, and $ zipWith close (map snd best) (map snd expectedBest))
                        `shouldBe` (reach, count, length expectedBest, True)
        it "gives each term within the bound a probability, and the probabilities sum to one" $
            forM_ mixtures $ \(reach, mixture) -> do
                (reach, close (sum $ map (probability mixture) terms) 1) `shouldBe` (reach, True)
                forM_ [Term.Node "outside" [], iterate (Term.Node "neg" . pure) (Term.Node "x" []) !! 5] $ \term ->
                    (reach, term, Mixture.termLogProbability mixture term) `shouldBe` (reach, term, Nothing)
        it "gives each next token the probability of its completions" $
            forM_ mixtures $ \(reach, mixture) ->
                forM_ prefixes $ \prefix -> do
                    let within = [(preorder term, probability mixture term) | term <- terms, prefix `isPrefixOf` preorder term]
                        total = sum $ map snd within
                        expected =
                            Map.toList $
                                Map.fromListWith
                                    (+)
                                    [(tokens !! length prefix, value / total) | (tokens, value) <- within, length tokens > length prefix]
                        found = fromJust $ Mixture.nextTokenProbabilities mixture prefix
                    (reach, prefix, map fst found) `shouldBe` (reach, prefix, map fst expected)
                    (reach, prefix, and $ zipWith close (map snd found) (map snd expected)) `shouldBe` (reach, prefix, True)
        it "gives each component a probability after a prefix: the mean of its probabilities after the next tokens" $
            forM_ mixtures $ \(reach, mixture) ->
                forM_ prefixes $ \prefix -> do
                    let components = fromJust $ Mixture.componentProbabilities mixture prefix
                        next = fromJust $ Mixture.nextTokenProbabilities mixture prefix
                        later =
                            [ map (* value) $ fromJust $ Mixture.componentProbabilities mixture (prefix <> [token])
                            | (token, value) <- next
                            ]
                    (reach, prefix, length components, close (sum components) 1) `shouldBe` (reach, prefix, 2, True)
                    (reach, prefix, null next || and (zipWith close components $ foldr1 (zipWith (+)) later))
                        `shouldBe` (reach, prefix, True)
        it "learns that the leaves of a term are equal, which one model cannot learn" $
            forM_ mixtures $ \(reach, mixture) -> do
                let model = fromJust $ Model.train reach expressions 5 (only "x" <> only "y")
                    single = exp . fromJust . Model.termLogProbability model
                    equal value = value (negated "x" "x") * value (negated "y" "y")
                    different value = value (negated "x" "y") * value (negated "y" "x")
                -- The four terms have the same sum of counts, so one table of weights gives the same product.
                (reach, close (different single) (equal single)) `shouldBe` (reach, True)
                (reach, different (probability mixture) < equal (probability mixture) / 16) `shouldBe` (reach, True)
        it "moves the terms of an incorrect split to their component" $
            forM_ (take 2 reaches) $ \reach -> do
                -- Six of the terms with y are in the group of the terms with x.
                let mixture = fromJust $ Mixture.train reach expressions 5 [only "x" <> take 6 (only "y"), drop 6 $ only "y"]
                    shares = fromJust . Mixture.componentProbabilities mixture
                (reach, map ((< 0.05) . abs . subtract 0.5) $ shares []) `shouldBe` (reach, [True, True])
                (reach, map (> 0.9) $ shares $ preorder $ negated "x" "x") `shouldBe` (reach, [True, False])
                (reach, map (> 0.9) $ shares $ preorder $ negated "y" "y") `shouldBe` (reach, [False, True])
        it "samples each completion of a prefix with its probability" $
            forM_ mixtures $ \(reach, mixture) -> do
                forM_ [[], [("add", 2)], [("add", 2), ("neg", 1), ("y", 0)]] $ \prefix -> do
                    let within = [term | term <- terms, prefix `isPrefixOf` preorder term]
                        total = sum $ map (probability mixture) within
                        drawn = Map.fromListWith (+) [(term, mass) | (mass, term) <- runExact $ fromJust $ Mixture.lowerTerm mixture prefix]
                    (reach, prefix, Map.keys drawn, sum drawn) `shouldBe` (reach, prefix, sort within, 1)
                    forM_ (Map.toList drawn) $ \(term, mass) ->
                        (reach, prefix, term, close (fromRational mass) (probability mixture term / total))
                            `shouldBe` (reach, prefix, term, True)
                    let sampled = QCGen.unGen (QC.vectorOf 50 $ fromJust $ Mixture.sampleTerm mixture prefix) (QCRandom.mkQCGen 3) 30
                    (reach, prefix, filter (not . isPrefixOf prefix . preorder) sampled) `shouldBe` (reach, prefix, [])
                (reach, isNothing $ Mixture.sampleTerm mixture [("x", 0), ("y", 0)]) `shouldBe` (reach, True)
        it "gives the completions of a prefix with the largest probabilities, the most probable first" $
            forM_ mixtures $ \(reach, mixture) -> do
                forM_ prefixes $ \prefix -> do
                    let within = Map.fromList [(term, probability mixture term) | term <- terms, prefix `isPrefixOf` preorder term]
                        total = sum within
                        expected = sortOn Down $ map (/ total) $ Map.elems within
                        near left right = abs (left - right) < 1e-9
                        every = fromJust $ Mixture.bestTerms (Map.size within + 1) mixture prefix
                    forM_ [1, 2, 5, Map.size within + 1] $ \count -> do
                        let found = fromJust $ Mixture.bestTerms count mixture prefix
                        (reach, prefix, count, length found, and $ zipWith near (map snd found) expected)
                            `shouldBe` (reach, prefix, count, min count (Map.size within), True)
                        forM_ found $ \(term, value) ->
                            (reach, prefix, count, term, near value . (/ total) <$> Map.lookup term within)
                                `shouldBe` (reach, prefix, count, term, Just True)
                        (reach, prefix, count, nubOrd $ map fst found) `shouldBe` (reach, prefix, count, map fst found)
                        -- The order is fixed, so a smaller count gives the first completions of a larger count.
                        (reach, prefix, count, found) `shouldBe` (reach, prefix, count, take count every)
                (reach, Mixture.bestTerms 1 mixture [("x", 0), ("y", 0)]) `shouldBe` (reach, Nothing)
                (reach, map (\count -> Mixture.bestTerms count mixture []) [0, -1]) `shouldBe` (reach, [Just [], Just []])
        it "gives each term of an event its probability over the probability of the event, and draws it with this exact mass" $
            forM_ given $ \(reach, name, event, mixture, conditioned) -> do
                let inEvent = filter (FTA.accepts event) terms
                    total = sum $ map (probability mixture) inEvent
                    drawn = masses conditioned
                forM_ terms $ \term ->
                    (reach, name, term, close (probability mixture term / total) . exp <$> Mixture.termLogProbability conditioned term)
                        `shouldBe` (reach, name, term, if FTA.accepts event term then Just True else Nothing)
                (reach, name, Map.keys drawn, sum drawn) `shouldBe` (reach, name, sort inEvent, 1)
                forM_ (Map.toList drawn) $ \(term, mass) ->
                    (reach, name, term, close (fromRational mass) (probability conditioned term)) `shouldBe` (reach, name, term, True)
        it "multiplies the share of each component by the probability of the event in the component" $
            forM_ given $ \(reach, name, event, mixture, conditioned) -> do
                -- For each component, the probability of the component and the event: the sum, over the terms of the
                -- event, of the probability of the term times the probability of the component after the term.
                let joint =
                        foldr1
                            (zipWith (+))
                            [ map (* probability mixture term) $ fromJust $ Mixture.componentProbabilities mixture (preorder term)
                            | term <- terms
                            , FTA.accepts event term
                            ]
                (reach, name, zipWith close (map (/ sum joint) joint) <$> Mixture.componentProbabilities conditioned [])
                    `shouldBe` (reach, name, Just [True, True])
        it "keeps each probability given an event that each term is in" $
            forM_ mixtures $ \(reach, mixture) -> do
                let conditioned = fromJust $ Mixture.condition expressions mixture
                (reach, masses conditioned) `shouldBe` (reach, masses mixture)
                forM_ terms $ \term ->
                    (reach, term, close (probability mixture term) (probability conditioned term)) `shouldBe` (reach, term, True)
                forM_ prefixes $ \prefix -> do
                    (reach, prefix, Mixture.eventProbability mixture prefix) `shouldBe` (reach, prefix, Just 1)
                    (reach, prefix, close 1 <$> Mixture.eventProbability conditioned prefix) `shouldBe` (reach, prefix, Just True)
        it "gives the probability of an event after each prefix, as the sums over the terms give it, and the lookahead" $
            forM_ given $ \(reach, name, event, mixture, conditioned) -> do
                let after = Map.fromList [(prefix, Mixture.eventProbability conditioned prefix) | prefix <- prefixes]
                    probabilityAfter prefix = fromJust $ after Map.! prefix
                forM_ prefixes $ \prefix -> do
                    let within = [(probability mixture term, FTA.accepts event term) | term <- terms, prefix `isPrefixOf` preorder term]
                        inEvent = sum [value | (value, True) <- within]
                    if inEvent == 0
                        then (reach, name, prefix, after Map.! prefix) `shouldBe` (reach, name, prefix, Just 0)
                        else
                            (reach, name, prefix, close (inEvent / sum (map fst within)) <$> after Map.! prefix)
                                `shouldBe` (reach, name, prefix, Just True)
                    -- P(x | p, E) P(E | p) = P(x | p) P(E | p <> [x])
                    let lookahead = fromMaybe [] $ Mixture.nextTokenProbabilities conditioned prefix
                    forM_ (fromJust $ Mixture.nextTokenProbabilities mixture prefix) $ \(token, value) ->
                        ( reach
                        , name
                        , prefix
                        , token
                        , close
                            (fromMaybe 0 (lookup token lookahead) * probabilityAfter prefix)
                            (value * probabilityAfter (prefix <> [token]))
                        )
                            `shouldBe` (reach, name, prefix, token, True)
                forM_ [[("x", 0), ("y", 0)], [("neg", 2)]] $ \prefix ->
                    (reach, name, prefix, Mixture.eventProbability conditioned prefix) `shouldBe` (reach, name, prefix, Nothing)
        it "gives the mixture given both events when it conditions twice" $
            forM_ mixtures $ \(reach, mixture) -> do
                let twice = fromJust $ Mixture.condition rootAdd =<< Mixture.condition withoutY mixture
                    both =
                        FTA.intersectWith (\left right -> if left == right then Just left else Nothing) (\_ _ -> noConstraint) withoutY rootAdd
                    once = fromJust $ Mixture.condition both mixture
                (reach, masses twice) `shouldBe` (reach, masses once)
                forM_ prefixes $ \prefix ->
                    (reach, prefix, close <$> Mixture.eventProbability twice prefix <*> Mixture.eventProbability once prefix)
                        `shouldBe` (reach, prefix, Just True)
        it "is the model given the event when the corpus has one group" $
            forM_ reaches $ \reach -> do
                let mixture = fromJust $ Mixture.train reach expressions 5 [corpus]
                    model = fromJust $ Model.train reach expressions 5 corpus
                forM_ events $ \(name, event) -> do
                    let conditioned = fromJust $ Mixture.condition event mixture
                        expected = fromJust $ Model.condition event model
                    forM_ terms $ \term ->
                        ( reach
                        , name
                        , term
                        , close <$> fmap exp (Mixture.termLogProbability conditioned term) <*> fmap exp (Model.termLogProbability expected term)
                        )
                            `shouldBe` (reach, name, term, if FTA.accepts event term then Just True else Nothing)
                    forM_ prefixes $ \prefix ->
                        (reach, name, prefix, close <$> Mixture.eventProbability conditioned prefix <*> Model.eventProbability expected prefix)
                            `shouldBe` (reach, name, prefix, Just True)
        it "gives no mixture for an event with a constraint or without a term in the bound" $
            forM_ mixtures $ \(reach, mixture) -> do
                (reach, isNothing $ Mixture.condition doubles mixture) `shouldBe` (reach, True)
                -- A term with six nodes, beyond the bound.
                let deep = iterate (Term.Node "neg" . pure) (Term.Node "x" []) !! 5
                (reach, isNothing $ Mixture.condition (FTA.fromTerms [deep]) mixture) `shouldBe` (reach, True)

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

-- | The event that a term has no y.
withoutY :: FTA.FTA String String Constraint
withoutY =
    either (error . show) id $
        FTA.mkFTA "e" [("e", [node "x" [], node "neg" ["e"], node "add" ["e", "e"]])]
  where
    node symbol children = FTA.Transition symbol children noConstraint

-- | The event that the root is add. The terms add(x, e) and add(y, e) have two runs: an ambiguous event.
rootAdd :: FTA.FTA String String Constraint
rootAdd =
    either (error . show) id $
        FTA.mkFTA
            "r"
            [ ("r", [node "add" ["e", "e"], node "add" ["v", "e"]])
            , ("e", [node "x" [], node "y" [], node "neg" ["e"], node "add" ["e", "e"]])
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
