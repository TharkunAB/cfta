module Data.CFTA.Mask.VocabularySpec (spec) where

import Control.Monad (foldM, forM_)
import Data.List (inits)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Gen as QCGen
import qualified Test.QuickCheck.Random as QCRandom

import qualified Data.CFTA as FTA
import Data.CFTA.Gen.ExpressionLanguage (
    equalTextMask,
    expressionText,
    singleParenthesesAutomaton,
    singleParenthesesTextMask,
 )
import Data.CFTA.Gen.ExpressionLanguageSpec (leaf, node, structuralTexts)
import Data.CFTA.Guided
import Data.CFTA.Mask
import Data.CFTA.Mask.Text
import Data.CFTA.Mask.TextSpec (alphabet, lazyMask, limits, pairTexts, prefixCounts, singleTexts)
import Data.CFTA.Mask.Vocabulary
import Data.CFTA.Sized.Prefix (prefixCompletionsWith)
import Data.CFTA.Sized.PrefixGuardSpec (guardedPairs, partialEntailment)
import Data.CFTA.Term (Term)

spec :: Spec
spec = describe "Data.CFTA.Mask.Vocabulary" $ do
    it "offers the entries that continue a text at each prefix of a walk, with the ratios of their counts" $ do
        let walks = QCGen.unGen (QC.vectorOf 100 $ walk entryStart) (QCRandom.mkQCGen 20261114) 30
        sum (map (length . snd) walks) `shouldSatisfy` (> 300)
        forM_ walks $ \(taken, masks) -> forM_ (zip (inits taken) masks) $ \(prefix, mask) -> do
            let tokens = concatMap tokensOf prefix
                ended = EndOfText `elem` tokens
            maskPrefix mask `shouldBe` prefix
            (prefix, maskNext mask)
                `shouldBe` (prefix, [(name, ratio tokens after) | (name, after) <- entries, behind (tokens <> after) > 0])
            (prefix, maskUndecided mask) `shouldBe` (prefix, [])
            (prefix, map expressionText $ maskTerms mask) `shouldBe` (prefix, [[character | Character character <- tokens] | ended])
            -- The entries with one token are the tokens of the mask below, so their probabilities sum to one.
            (prefix, sum [probability | (name, probability) <- maskNext mask, length (tokensOf name) == 1])
                `shouldBe` (prefix, if ended then 0 else 1)

    it "ends after an entry whose last token is the end of the text, with the term of the text" $ do
        let expression = node '(' [node '+' [node '(' [leaf 'a'], node '(' [leaf 'a']]]
            body = through entryStart $ map named ["(", "(a", ")", "+", "(a"]
            ends =
                [ [named "))", entryOf [EndOfText]]
                , map named [")", ")"] <> [entryOf [EndOfText]]
                , [named ")", entryOf [Character ')', EndOfText]]
                ]
        forM_ ends $ \ending -> do
            let ended = through body ending
            map fst (maskNext ended) `shouldBe` []
            maskTerms ended `shouldBe` [expression]
            map (refusalOf ended . fst) entries `shouldBe` (Just PrefixEnded <$ entries)

    it "offers a and refuses b after a+, and refuses the entry a+b, so no entry writes a sum with two different children" $ do
        let equalStart = vocabularyMask (vocabulary entries) equalTextMask
            afterSum = through equalStart [named "a+"]
        map fst (maskNext afterSum) `shouldSatisfy` elem (named "a")
        map fst (maskNext afterSum) `shouldSatisfy` notElem (named "b")
        refusalOf afterSum (named "a") `shouldBe` Nothing
        refusalOf afterSum (named "b") `shouldBe` Just TokenRejected
        map fst (maskNext equalStart) `shouldSatisfy` notElem (named "a+b")
        refusalOf equalStart (named "a+b") `shouldBe` Just TokenRejected

    it "offers the entries a and b after a+ without the equality, and only a with it" $ do
        let entriesOf = vocabulary [(1 :: Int, [Character 'a']), (2, [Character 'b']), (3, [EndOfText])]
            offeredAfter texts written =
                either (const []) (map fst . maskNext . vocabularyMask entriesOf) $ foldM maskStep texts $ map Character written
        offeredAfter structuralTexts "a+" `shouldBe` [1, 2]
        offeredAfter equalTextMask "a+" `shouldBe` [1]
        offeredAfter equalTextMask "a+a" `shouldBe` [3]
        offeredAfter equalTextMask "a+b" `shouldBe` []
        let entryMask =
                vocabularyMask
                    (vocabulary [(0 :: Int, map Character "a+"), (1, [Character 'a']), (2, [Character 'b']), (3, [EndOfText])])
                    equalTextMask
        map fst (maskNext entryMask) `shouldBe` [0, 1, 2]
        fmap (map fst . maskNext) (maskStep entryMask 0) `shouldBe` Right [1]

    it "refuses an unknown entry and an entry without tokens, and offers two entries with the same tokens" $ do
        let withoutTokens = length entries
            missing = withoutTokens + 1
            withEmpty = vocabularyMask (vocabulary $ entries <> [(withoutTokens, [])]) singleParenthesesTextMask
            (_, masks) = QCGen.unGen (walk withEmpty) (QCRandom.mkQCGen 20261114) 30
        forM_ masks $ \mask -> do
            map fst (maskNext mask) `shouldSatisfy` all (`notElem` [withoutTokens, missing])
            map (refusalOf mask) [withoutTokens, missing] `shouldBe` [Just TokenRejected, Just TokenRejected]
        let sums = [name | (name, tokens) <- entries, tokens == map Character "a+"]
        length sums `shouldBe` 2
        filter ((`elem` sums) . fst) (maskNext entryStart)
            `shouldBe` [(name, ratio [] $ map Character "a+") | name <- sums]

    -- After (, the next character is (, a, or b, so the entry ( and the
    -- entries ((, (a, and (b, which start with (, are offered.
    it "offers an entry and the entries that start with it, so the probabilities sum to more than one" $ do
        let offered = maskNext entryStart
            probability = fromMaybe 0 . (`lookup` offered) . named
        map probability ["(", "((", "(a", "(b"]
            `shouldBe` map (ratio [] . map Character) ["(", "((", "(a", "(b"]
        probability "(" `shouldBe` probability "((" + probability "(a" + probability "(b"
        sum (map snd offered) `shouldSatisfy` (> 1)

    it "gives TokenUndecided for an entry whose undecided token comes after decided tokens, with a solver" $ do
        pairs <- textMask pairTexts . completionsMask <$> prefixCompletionsWith partialEntailment 3 guardedPairs
        let entryMask = vocabularyMask (vocabulary $ zip [0 :: Int ..] $ map (map Character) ["g(2", "g(3", "g(1", "g(3, 2)", "g("]) pairs
        (map fst $ maskNext entryMask, maskUndecided entryMask) `shouldBe` ([0, 4], [1, 3])
        map (refusalOf entryMask) [0, 1, 2, 3]
            `shouldBe` [Nothing, Just TokenUndecided, Just TokenRejected, Just TokenUndecided]

    it "runs the guided search on the entries, and each found term has no double parentheses" $ do
        (greedy, _) <- guide Greedy (limits 1) MaskOnly entryScorer emptyMaskCache entryStart
        (bestFirst, _) <- guide BestFirst (limits 3) MaskOnly entryScorer emptyMaskCache entryStart
        (guidedStop greedy, guidedStop bestFirst) `shouldBe` (EnoughTerms, EnoughTerms)
        map (length . guidedTerms) [greedy, bestFirst] `shouldBe` [1, 3]
        map (FTA.accepts singleParenthesesAutomaton . fst) (guidedTerms greedy <> guidedTerms bestFirst)
            `shouldSatisfy` and

    it "steps the mask below only for the tokens of the entries, and reads no probability to offer an entry" $ do
        let gOnly = vocabulary [(0 :: Int, [("g", 0)])]
            unread = lazyMask{maskNext = [(token, error "a probability") | (token, _) <- maskNext lazyMask]}
        maskNext (vocabularyMask gOnly lazyMask) `shouldBe` [(0, 1 / 2)]
        fmap maskTerms (maskStep (vocabularyMask gOnly lazyMask) 0) `shouldBe` Right [()]
        map fst (maskNext $ vocabularyMask gOnly unread) `shouldBe` [0]

{- | The tokens of each entry of the vocabulary of the texts without double
parentheses, by the name of the entry: each character of the texts, longer
entries, the end of the text, and a closing parenthesis with the end of the
text.
-}
entries :: [(Int, [TextToken])]
entries =
    zip [0 ..] $
        map (map Character) (map pure alphabet <> longer) <> [[EndOfText], [Character ')', EndOfText]]
  where
    -- Two entries have the tokens of a+, and the entry a+b writes a sum with two different children.
    longer = ["a+", "a+", "((", "(a", "(b", "))", "a+b"]

-- | The mask of the entries of the vocabulary of the texts without double parentheses.
entryStart :: Mask Int (Term Char)
entryStart = vocabularyMask (vocabulary entries) singleParenthesesTextMask

-- | The name of the first entry with these tokens.
entryOf :: [TextToken] -> Int
entryOf tokens = fromMaybe (error $ "no entry " <> show tokens) $ lookup tokens [(after, name) | (name, after) <- entries]

-- | The name of the first entry whose tokens are the characters of a text.
named :: String -> Int
named = entryOf . map Character

-- | The tokens of an entry.
tokensOf :: Int -> [TextToken]
tokensOf name = fromMaybe (error $ "no entry " <> show name) $ lookup name entries

-- | The mask after the steps of the entries. The masks must offer each entry.
through :: Mask Int term -> [Int] -> Mask Int term
through = foldl (\mask entry -> either (error . show) id $ maskStep mask entry)

-- | The refusal of an entry, or 'Nothing' when the mask offers it.
refusalOf :: Mask entry term -> entry -> Maybe Refusal
refusalOf mask = either Just (const Nothing) . maskStep mask

{- | The number of the texts without double parentheses whose tokens, with
'EndOfText' at the end, start with these tokens.
-}
behind :: [TextToken] -> Int
behind tokens = case break (== EndOfText) tokens of
    (characters, []) -> Map.findWithDefault 0 (letters characters) prefixCounts
    (characters, [EndOfText]) -> if Set.member (letters characters) singleTexts then 1 else 0
    _ -> 0
  where
    letters characters = [character | Character character <- characters]

{- | The number of the texts without double parentheses behind a prefix and
the tokens after it, divided by the number behind the prefix.
-}
ratio :: [TextToken] -> [TextToken] -> Rational
ratio prefix after = fromIntegral (behind $ prefix <> after) / fromIntegral (behind prefix)

{- | A walk of a decoder through the offered entries, until the mask offers no
entry: the entries that it takes, and the masks on its way, the empty prefix
first.
-}
walk :: Mask Int term -> QC.Gen ([Int], [Mask Int term])
walk mask = case maskNext mask of
    [] -> pure ([], [mask])
    offered -> do
        (entry, _) <- QC.elements offered
        (taken, masks) <- walk $ either (error . show) id $ maskStep mask entry
        pure (entry : taken, mask : masks)

-- | Scores that prefer the entries with more tokens.
entryScorer :: Scorer Int
entryScorer _ = pure [(name, fromIntegral $ length tokens) | (name, tokens) <- entries]
