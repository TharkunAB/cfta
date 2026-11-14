module Data.CFTA.GuidedSpec (spec) where

import Control.Monad (forM_)
import Data.List (inits, sort, sortOn)
import Data.Maybe (fromMaybe)
import Data.Ord (Down (..))
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as FTA
import Data.CFTA.Gen.UntypedExpressionLanguage (expressionAutomaton)
import Data.CFTA.Guided
import Data.CFTA.Index (Size (..))
import Data.CFTA.Mask (completionsMask)
import Data.CFTA.Sized.Prefix hiding (Token)
import Data.CFTA.Sized.PrefixGuardSpec (guardedPairs, number, partialEntailment, sym)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | A token of the untyped expressions.
type Token = (String, Int)

spec :: Spec
spec = describe "Data.CFTA.Guided" $ do
    it "masks a token outside the language that the scorer prefers, and greedy gives the best term" $ do
        result <- search Greedy (limits 1000 1) MaskOnly (scorer preferInvalid)
        accepted result
        map fst (guidedTerms result) `shouldBe` [Term.Node "zero" []]
        map fst (guidedTerms result) `shouldBe` map fst (take 1 $ ranked preferInvalid)
        case guidedTrace result of
            root : _ -> do
                fmap fst (best' $ visitScores root) `shouldBe` Just ("one", 2)
                visitMask root `shouldBe` [("add", 2), ("multiply", 2), ("one", 0), ("zero", 0)]
            [] -> fail "no visit"

    it "finds the five best terms best-first, as a brute force over the 74 terms" $ do
        result <- search BestFirst (limits 1000 5) MaskOnly (scorer byLength)
        accepted result
        guidedStop result `shouldBe` EnoughTerms
        let expected = take 5 $ ranked byLength
        map fst (guidedTerms result) `shouldBe` map fst expected
        zipWith (\(_, found) (_, score) -> abs (found - score) < 1e-9) (guidedTerms result) expected
            `shouldBe` replicate 5 True

    it "lists every term best-first when the limits allow it" $ do
        result <- search BestFirst (limits 1000 1000) MaskOnly (scorer byLength)
        accepted result
        guidedStop result `shouldBe` Exhausted
        length (guidedTerms result) `shouldBe` 74
        map snd (guidedTerms result) `shouldSatisfy` \scores -> and (zipWith (>=) scores (drop 1 scores))

    it "stops at the limits of the search, with the reason" $ do
        visited <- search BestFirst (limits 2 1000) MaskOnly (scorer byLength)
        (guidedStop visited, length $ guidedTrace visited) `shouldBe` (VisitLimit, 2)
        found <- search BestFirst (limits 1000 3) MaskOnly (scorer byLength)
        (guidedStop found, length $ guidedTerms found) `shouldBe` (EnoughTerms, 3)
        timed <- search BestFirst (limits 1000 1000){searchMicros = Just 0} MaskOnly (scorer byLength)
        (guidedStop timed, guidedTrace timed, guidedTerms timed) `shouldBe` (OutOfTime, [], [])

    it "has one record for each visit, with its choice" $ do
        result <- search Greedy (limits 1000 1) MaskOnly (scorer byLength)
        accepted result
        case guidedTerms result of
            [(term, _)] -> do
                -- Without a dead end, greedy visits each proper prefix of its found term once.
                let tokens = preorder term
                map visitPrefix (guidedTrace result) `shouldBe` take (length tokens) (inits tokens)
                map visitChoice (guidedTrace result) `shouldBe` map Just tokens
            other -> fail $ show other

    it "goes back to the best open prefix at a dead end" $ do
        -- The scorer prefers add at the root and scores nothing after it.
        let scores prefix
                | prefix == [("add", 2)] = []
                | otherwise = [(("add", 2), 3), (("multiply", 2), 2), (("zero", 0), 1), (("one", 0), 0)]
        result <- search Greedy (limits 1000 1) MaskOnly (pure . scores)
        accepted result
        [(visitPrefix record, visitChoice record) | record <- take 2 $ guidedTrace result]
            `shouldBe` [([], Just ("add", 2)), ([("add", 2)], Nothing)]
        map (take 1 . preorder . fst) (guidedTerms result) `shouldBe` [[("multiply", 2)]]

    it "reads the masks of a cache, and a repeated search adds none" $ do
        (first, cache) <- guide BestFirst (limits 1000 5) MaskOnly (scorer byLength) emptyMaskCache (completionsMask language)
        (again, cache') <- guide BestFirst (limits 1000 5) MaskOnly (scorer byLength) cache (completionsMask language)
        again `shouldBe` first
        maskCacheSize cache `shouldSatisfy` (> 1)
        maskCacheSize cache' `shouldBe` maskCacheSize cache

    describe "beam search" $ do
        it "finds each term with a beam that holds every prefix, and its five best are those of best-first" $ do
            beam <- search (Beam 1000) (limits 100000 1000) MaskOnly (scorer byLength)
            accepted beam
            (guidedStop beam, length $ guidedTerms beam) `shouldBe` (Exhausted, 74)
            bestFirst <- search BestFirst (limits 1000 5) MaskOnly (scorer byLength)
            let top = take 5 $ sortOn (Down . snd) $ guidedTerms beam
            map fst top `shouldBe` map fst (guidedTerms bestFirst)
            zipWith (\(_, found) (_, score) -> abs (found - score) < 1e-9) top (guidedTerms bestFirst)
                `shouldBe` replicate 5 True

        it "follows the best token with a beam of width one, as greedy does" $
            forM_ [preferInvalid, byLength] $ \scores -> do
                beam <- search (Beam 1) (limits 1000 1) MaskOnly (scorer scores)
                greedy <- search Greedy (limits 1000 1) MaskOnly (scorer scores)
                accepted beam
                (guidedTerms beam, guidedTrace beam) `shouldBe` (guidedTerms greedy, guidedTrace greedy)

        it "stops at the limit of visits" $ do
            beam <- search (Beam 3) (limits 4 1000) MaskOnly (scorer byLength)
            (guidedStop beam, length $ guidedTrace beam) `shouldBe` (VisitLimit, 4)

    describe "repair" $ do
        it "keeps the prefix before a refused token in the middle, and completes it" $ do
            (repaired, _) <-
                repair
                    BestFirst
                    (limits 1000 3)
                    MaskOnly
                    (scorer byLength)
                    emptyMaskCache
                    (completionsMask language)
                    [("add", 2), ("one", 0), ("three", 0), ("zero", 0)]
            repairedRefusal repaired `shouldBe` Just (2, TokenRejected)
            accepted $ repairedSearch repaired
            map (take 2 . preorder . fst) (guidedTerms $ repairedSearch repaired)
                `shouldBe` replicate 3 [("add", 2), ("one", 0)]

        it "gives a complete term as it is, without a visit" $ do
            (repaired, _) <-
                repair
                    BestFirst
                    (limits 1000 1)
                    MaskOnly
                    (scorer byLength)
                    emptyMaskCache
                    (completionsMask language)
                    [("add", 2), ("one", 0), ("zero", 0)]
            repairedRefusal repaired `shouldBe` Nothing
            guidedTerms (repairedSearch repaired) `shouldBe` [(Term.Node "add" [Term.Node "one" [], Term.Node "zero" []], 0)]
            guidedTrace (repairedSearch repaired) `shouldBe` []

        it "stops after a complete term at the next token, because the prefix is a whole term" $ do
            (repaired, _) <-
                repair
                    BestFirst
                    (limits 1000 1)
                    MaskOnly
                    (scorer byLength)
                    emptyMaskCache
                    (completionsMask language)
                    [("add", 2), ("one", 0), ("zero", 0), ("one", 0)]
            repairedRefusal repaired `shouldBe` Just (3, PrefixEnded)
            guidedTerms (repairedSearch repaired) `shouldBe` [(Term.Node "add" [Term.Node "one" [], Term.Node "zero" []], 0)]
            guidedTrace (repairedSearch repaired) `shouldBe` []

        it "searches from the empty prefix when the first token is refused" $ do
            (repaired, _) <-
                repair
                    BestFirst
                    (limits 1000 5)
                    MaskOnly
                    (scorer byLength)
                    emptyMaskCache
                    (completionsMask language)
                    [("one", 2), ("add", 2)]
            fromScratch <- search BestFirst (limits 1000 5) MaskOnly (scorer byLength)
            repairedRefusal repaired `shouldBe` Just (0, TokenRejected)
            repairedSearch repaired `shouldBe` fromScratch

    describe "with a solver" $ do
        it "stops a repair at an undecided token with its reason, and the search before it shows the token" $ do
            pairs <- prefixCompletionsWith partialEntailment 3 guardedPairs
            let undecided = (number 3, 0)
            (repaired, _) <-
                repair
                    BestFirst
                    (limits 1000 1000)
                    MaskOnly
                    uniformPairs
                    emptyMaskCache
                    (completionsMask pairs)
                    [(sym "g", 2), undecided, (number 1, 0)]
            repairedRefusal repaired `shouldBe` Just (1, TokenUndecided)
            case guidedTrace $ repairedSearch repaired of
                root : _ ->
                    (visitPrefix root, visitMask root, visitUndecided root)
                        `shouldBe` ([(sym "g", 2)], [(number 2, 0)], [undecided])
                [] -> fail "no visit"
            map (take 2 . preorder . fst) (guidedTerms $ repairedSearch repaired)
                `shouldBe` replicate 3 [(sym "g", 2), (number 2, 0)]

        it "ends at a dead end at a prefix whose tokens are all undecided, and the trace shows them" $ do
            pairs <- prefixCompletionsWith partialEntailment 3 guardedPairs
            let after = fromMaybe (error "a prefix of a term") $ afterPrefix pairs [(sym "g", 2), (number 3, 0)]
            (result, _) <- guide BestFirst (limits 1000 1000) MaskOnly uniformPairs emptyMaskCache (completionsMask after)
            (guidedTerms result, guidedStop result) `shouldBe` ([], Exhausted)
            [(visitMask record, sort $ visitUndecided record, visitChoice record) | record <- guidedTrace result]
                `shouldBe` [([], sort [(number value, 0) | value <- [1, 2, 3]], Nothing)]

    it "changes the choice with weights, as the probabilities of the weighted completions" $ do
        -- With the same score for each token, the weights decide.
        let uniform = const [(token, 0) | token <- [("add", 2), ("multiply", 2), ("one", 0), ("zero", 0)]]
            weights symbol = case symbol of
                "one" -> 10
                "zero" -> 1
                _ -> 1 / 100
            weightedLanguage = fromMaybe (error "a negative weight") $ withWeights weights language
            predicted =
                [ ( token
                  , maybe (-(1 / 0)) (log . fromRational) $ tokenProbability weightedLanguage token
                  )
                | token <- map fst $ nextTokens language
                ]
        plain <- search Greedy (limits 1000 1) MaskOnly (pure . uniform)
        (weighted, _) <-
            guide Greedy (limits 1000 1) WeighCompletions (pure . uniform) emptyMaskCache (completionsMask weightedLanguage)
        accepted plain
        accepted weighted
        map (map visitChoice . take 1 . guidedTrace) [plain, weighted] `shouldBe` [[Just ("add", 2)], [Just ("one", 0)]]
        case guidedTrace weighted of
            root : _ ->
                zipWith (\(_, found) (_, step) -> abs (found - step) < 1e-9) (visitSteps root) predicted `shouldBe` replicate 4 True
            [] -> fail "no visit"
        map fst (guidedTerms weighted) `shouldBe` [Term.Node "one" []]

-- | The untyped expressions with at most six nodes: 74 terms.
language :: Completions String
language = either (error . show) id $ prefixCompletions (Size 6) expressionAutomaton

-- | A guided search of the mask of 'language' from an empty mask cache.
search :: Strategy -> SearchLimits -> Weighing -> Scorer Token -> IO (Guided Token (Term String))
search strategy searchLimits weighing scores =
    fst <$> guide strategy searchLimits weighing scores emptyMaskCache (completionsMask language)

-- | The limits with the given visits and found terms, without a wall-clock time.
limits :: Int -> Int -> SearchLimits
limits visits terms = SearchLimits{searchVisits = visits, searchTerms = terms, searchMicros = Nothing}

-- | A scorer from scores of the prefix.
scorer :: ([Token] -> [(Token, Double)]) -> Scorer Token
scorer scores = pure . scores

-- | The same scores after each prefix: the most for @one@ with two children, which the language does not have.
preferInvalid :: [Token] -> [(Token, Double)]
preferInvalid _ = [(("one", 2), 5), (("zero", 0), 3), (("one", 0), 2), (("add", 2), 1), (("multiply", 2), 0)]

-- | Scores that change with the length of the prefix, so that no two terms have the same total.
byLength :: [Token] -> [(Token, Double)]
byLength prefix =
    [ (("add", 2), 1.5 - 0.43 * position)
    , (("multiply", 2), 0.29 * position)
    , (("one", 0), 0.7 + 0.31 * position)
    , (("zero", 0), 1.1 - 0.17 * position)
    ]
  where
    position = fromIntegral $ length prefix

-- | Each found term is a term of the automaton.
accepted :: Guided Token (Term String) -> IO ()
accepted result = map (FTA.accepts expressionAutomaton . fst) (guidedTerms result) `shouldSatisfy` and

-- | The terms of the language with their total log-scores, best first: a brute force over the masks of their prefixes.
ranked :: ([Token] -> [(Token, Double)]) -> [(Term String, Double)]
ranked scores = sortOn (Down . snd) [(term, total term) | term <- completionTerms language]
  where
    total term = sum [step prefix token | (prefix, token) <- zip (inits $ preorder term) (preorder term)]
    step prefix token =
        let completions = fromMaybe (error "a prefix of a term") $ afterPrefix language prefix
            score offeredToken = fromMaybe (-(1 / 0)) $ lookup offeredToken $ scores prefix
            finite = filter (not . isInfinite) [score offeredToken | (offeredToken, _) <- nextTokens completions]
         in score token - log (sum $ map exp finite)

-- | The token with the highest score.
best' :: [(Token, Double)] -> Maybe (Token, Double)
best' [] = Nothing
best' scores = Just $ foldr1 (\left right -> if snd left >= snd right then left else right) scores

-- | The same score for each token of 'guardedPairs'.
uniformPairs :: Scorer (Symbol, Int)
uniformPairs _ = pure [(token, 0) | token <- (sym "g", 2) : [(number value, 0) | value <- [1, 2, 3]]]

-- | The tokens of a term in preorder.
preorder :: Term symbol -> [(symbol, Int)]
preorder (Term.Node symbol children) = (symbol, length children) : concatMap preorder children
