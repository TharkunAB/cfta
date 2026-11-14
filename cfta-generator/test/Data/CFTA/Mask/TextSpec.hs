module Data.CFTA.Mask.TextSpec (spec) where

import Control.Monad (forM_)
import Data.Containers.ListUtils (nubOrd)
import Data.List (inits, sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Gen as QCGen
import qualified Test.QuickCheck.Random as QCRandom

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (noConstraint)
import Data.CFTA.Gen.ExpressionLanguage (equalAutomaton, expressionTexts)
import Data.CFTA.Gen.ExpressionLanguageSpec (
    allExpressions,
    equalCompletions,
    leaf,
    node,
    singleExpressions,
    singleParenthesesCompletions,
 )
import Data.CFTA.Guided
import Data.CFTA.Index (Size (..))
import Data.CFTA.Mask
import Data.CFTA.Mask.Text
import Data.CFTA.Sized.Prefix (completionTerms, prefixCompletions, prefixCompletionsWith)
import Data.CFTA.Sized.PrefixGuardSpec (guardedPairs, number, partialEntailment, sym)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term)

spec :: Spec
spec = describe "Data.CFTA.Mask.Text" $ do
    it "reads the text of each expression without double parentheses back to the expression alone" $
        forM_ singleExpressions $ \expression ->
            (expression, readText singleParenthesesTextMask $ expressionText expression)
                `shouldBe` (expression, Right [expression])

    it "refuses each text with double parentheses at the first character that no text without them shares" $ do
        let doubled = filter (`Set.notMember` Set.fromList singleExpressions) allExpressions
        length doubled `shouldBe` 418
        forM_ doubled $ \expression ->
            let written = expressionText expression
             in (written, refusal $ readText singleParenthesesTextMask written)
                    `shouldBe` (written, Just (sharedLength written, TokenRejected))

    it "offers the tokens of the texts at each prefix of a walk, with the ratios of their counts" $ do
        let walks = QCGen.unGen (QC.vectorOf 100 $ walk singleParenthesesTextMask) (QCRandom.mkQCGen 20261114) 30
        sum (map length walks) `shouldSatisfy` (> 300)
        forM_ (concat walks) $ \mask -> do
            let prefix = [character | Character character <- maskPrefix mask]
                count = fromIntegral . fromMaybe (0 :: Int) . (`Map.lookup` prefixCounts)
                expected =
                    [ (Character character, count (prefix <> [character]) / count prefix)
                    | character <- alphabet
                    , Map.member (prefix <> [character]) prefixCounts
                    ]
                        <> [(EndOfText, 1 / count prefix) | Set.member prefix singleTexts]
            (prefix, maskNext mask) `shouldBe` (prefix, expected)
            (prefix, sum $ map snd $ maskNext mask) `shouldBe` (prefix, 1)
            (prefix, maskUndecided mask, maskTerms mask) `shouldBe` (prefix, [], [])

    it "refuses the named sums with two different children at their places, and reads an expression back" $ do
        let refused = refusal . readText equalTextMask
        -- After a+, the right child of the sum must be a, so b is the first character that no text with the equality has.
        refused "a+b" `shouldBe` Just (2, TokenRejected)
        fmap textErrorExpected (either Just (const Nothing) $ readText equalTextMask "a+b") `shouldBe` Just [Character 'a']
        -- After (a)+(, the right child of the sum must be (a).
        refused "(a)+(b)" `shouldBe` Just (5, TokenRejected)
        -- The left child of this sum is a*b, and an atom is not a product, so no text with the equality has a*b+.
        refused "a*b+b" `shouldBe` Just (3, TokenRejected)
        fmap textErrorExpected (either Just (const Nothing) $ readText equalTextMask "a*b+b")
            `shouldBe` Just [Character '*', EndOfText]
        readText equalTextMask "a+a*b" `shouldBe` Right [node '*' [node '+' [leaf 'a', leaf 'a'], leaf 'b']]
        refusal (readText equalTextMask "a+a*b ") `shouldBe` Just (5, TokenRejected)

    describe "an infix language" $ do
        let sums = textMask infixTexts $ completionsMask $ either (error . show) id $ prefixCompletions (Size 5) infixAutomaton
            one = leaf "1"
            two = leaf "2"
        it "reads a text that two terms have as both terms" $
            fmap sort (readText sums "1 + 2 + 1")
                `shouldBe` Right (sort [node "add" [node "add" [one, two], one], node "add" [one, node "add" [two, one]]])
        it "offers the end and a space after the text 1" $
            fmap (map fst . maskNext) (maskStep sums $ Character '1') `shouldBe` Right [Character ' ', EndOfText]
        it "reads the text of each term back to a list with the term" $ do
            let terms = completionTerms $ either (error . show) id $ prefixCompletions (Size 5) infixAutomaton
            length terms `shouldBe` 74
            forM_ terms $ \term ->
                (term, fmap (elem term) $ readText sums $ fromMaybe (error "a term without a text") $ linearize infixTexts term)
                    `shouldBe` (term, Right True)

    it "steps the mask of the terms for a token only when a character selects it" $ do
        let lazy = textMask lazyTexts lazyMask
        maskNext lazy `shouldBe` [(Character 'f', 1 / 2), (Character 'g', 1 / 2)]
        fmap (map fst . maskNext) (maskStep lazy $ Character 'f') `shouldBe` Right [Character '(']
        readText lazy "g" `shouldBe` Right [()]

    it "runs the guided search on the texts, and the automaton with the equality accepts each found term" $ do
        (greedy, _) <- guide Greedy (limits 1) MaskOnly textScorer emptyMaskCache equalTextMask
        (bestFirst, _) <- guide BestFirst (limits 3) MaskOnly textScorer emptyMaskCache equalTextMask
        (guidedStop greedy, guidedStop bestFirst) `shouldBe` (EnoughTerms, EnoughTerms)
        map (length . guidedTerms) [greedy, bestFirst] `shouldBe` [1, 3]
        map (FTA.accepts equalAutomaton . fst) (guidedTerms greedy <> guidedTerms bestFirst)
            `shouldSatisfy` and

    it "gives TokenUndecided at the first character of an undecided token, with a solver" $ do
        pairs <- textMask pairTexts . completionsMask <$> prefixCompletionsWith partialEntailment 3 guardedPairs
        let afterPair = foldl (\mask character -> either (error . show) id $ maskStep mask $ Character character) pairs "g("
        (map fst $ maskNext afterPair, maskUndecided afterPair) `shouldBe` ([Character '2'], [Character '3'])
        refusal (readText pairs "g(3, 2)") `shouldBe` Just (2, TokenUndecided)
        refusal (readText pairs "g(1, 2)") `shouldBe` Just (2, TokenRejected)
        fmap length (readText pairs "g(2, 3)") `shouldBe` Right 1

-- | The mask of the texts of the expressions with the equality at the bound of their spec.
equalTextMask :: Mask TextToken (Term Char)
equalTextMask = textMask expressionTexts $ completionsMask equalCompletions

-- | The mask of the texts of the expressions without double parentheses at the bound of their spec.
singleParenthesesTextMask :: Mask TextToken (Term Char)
singleParenthesesTextMask = textMask expressionTexts $ completionsMask singleParenthesesCompletions

-- | The text of an expression.
expressionText :: Term Char -> String
expressionText = fromMaybe (error "an expression without a text") . linearize expressionTexts

-- | The texts of the expressions without double parentheses.
singleTexts :: Set.Set String
singleTexts = Set.fromList $ map expressionText singleExpressions

-- | The number of the expressions without double parentheses whose text starts with each prefix.
prefixCounts :: Map.Map String Int
prefixCounts = Map.fromListWith (+) [(prefix, 1) | written <- Set.toList singleTexts, prefix <- inits written]

-- | The characters of the texts without double parentheses, in ascending order.
alphabet :: String
alphabet = sort $ nubOrd $ concat $ Set.toList singleTexts

-- | The number of the first characters of a text whose prefixes the texts without double parentheses have.
sharedLength :: String -> Int
sharedLength = length . takeWhile (`Map.member` prefixCounts) . drop 1 . inits

-- | The place and the reason of a refusal.
refusal :: Either TextError [term] -> Maybe (Int, Refusal)
refusal = either (\failure -> Just (textErrorPlace failure, textErrorRefusal failure)) (const Nothing)

{- | A walk of a decoder: the masks of the text prefixes on its way, the empty
prefix first. At each step it takes an offered token, until it takes the end
of the text.
-}
walk :: Mask TextToken term -> QC.Gen [Mask TextToken term]
walk mask = do
    (token, _) <- QC.elements $ maskNext mask
    case token of
        EndOfText -> pure [mask]
        Character _ -> (mask :) <$> walk (either (error . show) id $ maskStep mask token)

-- | The limits of a search with the given number of found terms.
limits :: Int -> SearchLimits
limits found = SearchLimits{searchVisits = 5000, searchTerms = found, searchMicros = Nothing}

-- | Scores that prefer the end of the text, and then the characters with the lowest codes.
textScorer :: Scorer TextToken
textScorer _ =
    pure $
        (EndOfText, 0) : [(Character character, negate $ 3 * fromIntegral (fromEnum character)) | character <- [' ' .. '~']]

-- | The numbers 1 and 2 with the binary operators add and mul, over one state.
infixAutomaton :: FTA.PlainFTA String String
infixAutomaton =
    either (error . show) id $
        FTA.mkFTA
            "e"
            [
                ( "e"
                , [ FTA.Transition symbol children noConstraint
                  | (symbol, children) <- [("1", []), ("2", []), ("add", ["e", "e"]), ("mul", ["e", "e"])]
                  ]
                )
            ]

-- | The infix notation of 'infixAutomaton'.
infixTexts :: String -> [String]
infixTexts symbol = case symbol of
    "add" -> ["", " + ", ""]
    "mul" -> ["", " * ", ""]
    _ -> [symbol]

-- | A mask of the terms whose step fails for the token @f@, which has the first text @f(@.
lazyMask :: Mask (String, Int) ()
lazyMask =
    Mask
        { maskPrefix = []
        , maskNext = [(("f", 1), 1 / 2), (("g", 0), 1 / 2)]
        , maskUndecided = []
        , maskStep = \token ->
            if token == ("f", 1)
                then error "the step of f"
                else
                    Right
                        Mask{maskPrefix = [token], maskNext = [], maskUndecided = [], maskStep = const $ Left PrefixEnded, maskTerms = [()]}
        , maskTerms = []
        }

-- | The texts of the symbols of 'lazyMask'.
lazyTexts :: String -> [String]
lazyTexts symbol = if symbol == "f" then ["f(", ")"] else [symbol]

-- | The call notation of the pairs with a guard.
pairTexts :: Symbol -> [String]
pairTexts symbol
    | symbol == sym "g" = ["g(", ", ", ")"]
    | otherwise = [show value | value <- [1, 2, 3 :: Integer], symbol == number value]
