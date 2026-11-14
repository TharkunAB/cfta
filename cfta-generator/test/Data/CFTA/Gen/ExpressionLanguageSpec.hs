module Data.CFTA.Gen.ExpressionLanguageSpec (
    spec,
    equalCompletions,
    singleParenthesesCompletions,
    allExpressions,
    equalExpressions,
    singleExpressions,
    node,
    leaf,
) where

import Control.Monad (foldM, forM_)
import Data.Functor (void)
import Data.List (inits)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Gen as QCGen
import qualified Test.QuickCheck.Random as QCRandom

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint)
import Data.CFTA.Gen.ExpressionLanguage (
    equalAutomaton,
    expressionTexts,
    singleParenthesesAutomaton,
    structuralAutomaton,
 )
import Data.CFTA.Gen.Internal.Table (unambiguousRows)
import Data.CFTA.Index (Size (..))
import Data.CFTA.Mask (Mask (..), completionsMask)
import Data.CFTA.Mask.Text (TextError (..), TextToken (..), linearize, readText, textMask)
import Data.CFTA.Sized.Prefix
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | The largest number of nodes of an expression in these tests.
sizeBound :: Integer
sizeBound = 7

-- | The completions of the empty prefix of 'equalAutomaton'.
equalCompletions :: Completions Char
equalCompletions = either (error . show) id $ prefixCompletions (Size sizeBound) equalAutomaton

-- | The completions of the empty prefix of 'singleParenthesesAutomaton'.
singleParenthesesCompletions :: Completions Char
singleParenthesesCompletions = either (error . show) id $ prefixCompletions (Size sizeBound) singleParenthesesAutomaton

-- | The expressions of 'structuralAutomaton' up to the bound, the sums with two different children included.
allExpressions :: [Term Char]
allExpressions =
    completionTerms . either (error . show) id $ prefixCompletions (Size sizeBound) structuralAutomaton

-- | The expressions up to the bound that have no sum with two different children.
equalExpressions :: [Term Char]
equalExpressions = filter (not . hasUnequalSum) allExpressions

{- | Whether a term has a sum with two different children as a subterm. This
predicate does not use the constraint.
-}
hasUnequalSum :: Term Char -> Bool
hasUnequalSum (Term.Node symbol children) =
    (symbol == '+' && isUnequal children) || any hasUnequalSum children
  where
    isUnequal [left, right] = left /= right
    isUnequal _ = False

-- | The expressions up to the bound that have no double parentheses.
singleExpressions :: [Term Char]
singleExpressions = filter (not . hasDoubleParentheses) allExpressions

{- | Whether a term has double parentheses, parentheses directly around
parentheses, as a subterm. This predicate does not use the template.
-}
hasDoubleParentheses :: Term Char -> Bool
hasDoubleParentheses (Term.Node symbol children) =
    (symbol == '(' && any isParentheses children) || any hasDoubleParentheses children
  where
    isParentheses (Term.Node child _) = child == '('

-- | The mask of the texts of the expressions of 'structuralAutomaton' up to the bound.
structuralTexts :: Mask TextToken (Term Char)
structuralTexts =
    textMask expressionTexts . completionsMask . either (error . show) id $
        prefixCompletions (Size sizeBound) structuralAutomaton

-- | The mask of the texts of the expressions of 'equalAutomaton' up to the bound.
equalTexts :: Mask TextToken (Term Char)
equalTexts = textMask expressionTexts $ completionsMask equalCompletions

-- | The mask of the texts of the expressions of 'singleParenthesesAutomaton' up to the bound.
singleTexts :: Mask TextToken (Term Char)
singleTexts = textMask expressionTexts $ completionsMask singleParenthesesCompletions

-- | The text of an expression.
text :: Term Char -> String
text = fromMaybe (error "an expression without a text") . linearize expressionTexts

-- | The tokens of a term in preorder.
preorder :: Term Char -> [(Char, Int)]
preorder (Term.Node symbol children) = (symbol, length children) : concatMap preorder children

-- | A term from its symbols and its children.
node :: symbol -> [Term symbol] -> Term symbol
node = Term.Node

-- | A term with no children.
leaf :: symbol -> Term symbol
leaf symbol = node symbol []

-- | Every non-empty prefix of the preorder of each expression of 'equalExpressions'.
equalPrefixes :: Set.Set [(Char, Int)]
equalPrefixes = Set.fromList [prefix | term <- equalExpressions, prefix <- drop 1 $ inits $ preorder term]

{- | The place of the first token of a preorder after which no expression of
'equalExpressions' starts with the tokens so far, if there is one.
-}
firstDeadPlace :: [(Char, Int)] -> Maybe Int
firstDeadPlace tokens =
    lookup False [(Set.member prefix equalPrefixes, place) | (place, prefix) <- zip [0 ..] $ drop 1 $ inits tokens]

-- | The result of a step through the preorder of a term, without the completions.
stepped :: Term Char -> Either (Int, Refusal) ()
stepped = void . stepPrefix equalCompletions . preorder

-- | Whether the rows of an automaton are unambiguous.
unambiguous :: (Ord state, Ord symbol) => FTA.FTA state symbol Constraint -> Bool
unambiguous = unambiguousRows . Map.map (map void) . FTA.transitionTable

{- | A walk of a decoder: at each step it takes a token of the mask, until the
prefix is complete. The result is the last completions with each prefix on
the way followed by each token of its mask.
-}
walk :: Completions Char -> QC.Gen (Completions Char, [[(Char, Int)]])
walk completions
    | isComplete completions = pure (completions, [])
    | otherwise = case nextTokens completions of
        [] -> error "a prefix that is not complete has no next token"
        offered -> do
            (token, _) <- QC.elements offered
            next <- either (error . show) pure $ stepToken completions token
            (done, seen) <- walk next
            pure (done, [completionPrefix completions <> [offeredToken] | (offeredToken, _) <- offered] <> seen)

spec :: Spec
spec = describe "Data.CFTA.Gen.ExpressionLanguage" $ do
    it "has unambiguous rows, so the mask reads the size index" $
        unambiguous singleParenthesesAutomaton `shouldBe` True
    it "lists the expressions up to the bound" $
        (length allExpressions, length equalExpressions) `shouldBe` (1286, 472)
    it "offers a and b after + a without the equality, and only a with it" $ do
        let structural = either (error . show) id $ prefixCompletions (Size sizeBound) structuralAutomaton
            sumOfA = [('+', 2), ('a', 0)]
        fmap (map fst . nextTokens) (stepPrefix structural sumOfA) `shouldBe` Right [('(', 1), ('a', 0), ('b', 0)]
        fmap (map fst . nextTokens) (stepPrefix equalCompletions sumOfA) `shouldBe` Right [('a', 0)]
    it "offers a and b after the text a+ without the equality, and refuses b with it" $ do
        fmap (map fst . maskNext) (foldM maskStep structuralTexts $ map Character "a+")
            `shouldBe` Right [Character '(', Character 'a', Character 'b']
        readText structuralTexts "a+b" `shouldBe` Right [node '+' [leaf 'a', leaf 'b']]
        readText equalTexts "a+b" `shouldBe` Left (TextError 2 TokenRejected [Character 'a'])
    it "reads the text of each expression back to the expression alone" $
        forM_ allExpressions $ \expression ->
            (text expression, readText structuralTexts $ text expression) `shouldBe` (text expression, Right [expression])
    -- The text (( is the start of the text ((a)+a), so the mask of the texts offers the second (.
    it "refuses the text ((a)) at its second ), because the text (( also starts ((a)+a)" $ do
        readText singleTexts "((a))" `shouldBe` Left (TextError 4 TokenRejected [Character '*', Character '+'])
        readText singleTexts "((a)+a)" `shouldBe` Right [node '(' [node '+' [node '(' [leaf 'a'], leaf 'a']]]
    it "accepts an expression token by token, and the result is the expression alone" $ do
        let expression = node '*' [node '+' [node '(' [leaf 'a'], node '(' [leaf 'a']], leaf 'b']
            tokens = preorder expression
        forM_ (zip [0 ..] tokens) $ \(place, token) ->
            fmap (map fst . nextTokens) (stepPrefix equalCompletions $ take place tokens) `shouldSatisfy` any (elem token)
        let done = stepPrefix equalCompletions tokens
        fmap isComplete done `shouldBe` Right True
        fmap completionTerms done `shouldBe` Right [expression]
    it "refuses a sum with two different children at the token where the children differ" $ do
        stepped (node '+' [leaf 'a', leaf 'b']) `shouldBe` Left (2, TokenRejected)
        stepped (node '*' [node '+' [leaf 'a', leaf 'b'], leaf 'a']) `shouldBe` Left (3, TokenRejected)
    it "refuses such a sum in parentheses, and accepts a product with two different children" $ do
        stepped (node '(' [node '+' [leaf 'a', leaf 'b']]) `shouldBe` Left (3, TokenRejected)
        stepped (node '(' [node '*' [leaf 'a', leaf 'b']]) `shouldBe` Right ()
        stepped (node '+' [node '(' [leaf 'b'], node '(' [leaf 'b']]) `shouldBe` Right ()
    it "refuses the second ( after ( as a token, so no expression has double parentheses" $ do
        let single = stepPrefix singleParenthesesCompletions
        fmap (map fst . nextTokens) (single [('(', 1)]) `shouldBe` Right [('*', 2), ('+', 2), ('a', 0), ('b', 0)]
        void (single $ preorder $ node '(' [node '(' [leaf 'a']]) `shouldBe` Left (1, TokenRejected)
        void (single $ preorder $ node '+' [leaf 'a', node '(' [node '(' [leaf 'b']]]) `shouldBe` Left (3, TokenRejected)
    it "counts the expressions as the brute force does" $
        completionCount equalCompletions `shouldBe` fromIntegral (length equalExpressions)
    it "counts the expressions without double parentheses as the brute force does" $ do
        length singleExpressions `shouldBe` 868
        completionCount singleParenthesesCompletions `shouldBe` fromIntegral (length singleExpressions)
        forM_ allExpressions $ \term ->
            (term, FTA.accepts singleParenthesesAutomaton term) `shouldBe` (term, not $ hasDoubleParentheses term)
    it "accepts an expression exactly when its sums have equal children, and otherwise refuses it at the first dead place" $
        forM_ allExpressions $ \term -> do
            let tokens = preorder term
                result = stepPrefix equalCompletions tokens
            (term, FTA.accepts equalAutomaton term) `shouldBe` (term, not $ hasUnequalSum term)
            case firstDeadPlace tokens of
                Nothing -> do
                    hasUnequalSum term `shouldBe` False
                    fmap isComplete result `shouldBe` Right True
                Just place -> do
                    hasUnequalSum term `shouldBe` True
                    void result `shouldBe` Left (place, TokenRejected)
    it "walks to an expression through offered tokens, and offers only the tokens that continue an expression" $ do
        let walks = QCGen.unGen (QC.vectorOf 200 $ walk equalCompletions) (QCRandom.mkQCGen 20261114) 30
        forM_ walks $ \(done, seen) -> do
            isComplete done `shouldBe` True
            seen `shouldSatisfy` all (`Set.member` equalPrefixes)
            fmap hasUnequalSum (completionTerms done) `shouldBe` [False]
            fmap (length . preorder) (completionTerms done) `shouldSatisfy` all (<= fromIntegral sizeBound)
