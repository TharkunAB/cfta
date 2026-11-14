module Data.CFTA.MaskSpec (spec) where

import Control.Monad (forM_, unless)
import Data.Containers.ListUtils (nubOrd)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint)
import Data.CFTA.Gen.ExpressionLanguage (singleParenthesesAutomaton)
import Data.CFTA.Gen.UntypedExpressionLanguage (expressionAutomaton)
import Data.CFTA.Index (Size (..))
import Data.CFTA.Mask
import Data.CFTA.Sized.Prefix
import Data.CFTA.Sized.PrefixGuardSpec (guardedPairs, partialEntailment, sym)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec = describe "Data.CFTA.Mask" $ do
    it "gives the mask of each prefix of the untyped expressions as their completions do" $
        agrees 6 (("absent", 0) : alphabet expressionAutomaton) (completions (Size 6) expressionAutomaton)
    -- The expressions without double parentheses, with the bound of their
    -- spec. The walk reaches each prefix, so the test also checks the refusal
    -- of the second ( after (.
    it "gives the mask of each prefix of the expressions without double parentheses as their completions do" $
        agrees 7 (('c', 0) : alphabet singleParenthesesAutomaton) (completions (Size 7) singleParenthesesAutomaton)
    it "gives the mask of each prefix of the pairs with a guard, with the undecided tokens" $ do
        pairs <- prefixCompletionsWith partialEntailment 3 guardedPairs
        agrees 3 ((sym "absent", 0) : alphabet guardedPairs) pairs

{- | For each prefix of at most the given number of tokens that a walk through
the offered tokens reaches, the mask agrees with the queries of the completions of the prefix: the offered tokens
with their probabilities, the undecided tokens, the step after each token of
the alphabet, and the term of a complete prefix.
-}
agrees :: (Ord symbol, Show symbol) => Int -> [Token symbol] -> Completions symbol -> IO ()
agrees depth tokens start =
    forM_ (reached depth start $ completionsMask start) $ \(current, mask) -> do
        let prefix = completionPrefix current
        (prefix, maskPrefix mask) `shouldBe` (prefix, prefix)
        (prefix, maskNext mask)
            `shouldBe` (prefix, [(token, fromMaybe 0 $ tokenProbability current token) | (token, _) <- nextTokens current])
        (prefix, maskUndecided mask) `shouldBe` (prefix, map fst $ undecidedTokens current)
        (prefix, map preorder $ maskTerms mask) `shouldBe` (prefix, [prefix | isComplete current])
        unless (isComplete current) $
            (prefix, sum $ map snd $ maskNext mask) `shouldBe` (prefix, 1)
        forM_ tokens $ \token ->
            (prefix, token, fmap maskPrefix $ maskStep mask token)
                `shouldBe` (prefix, token, fmap completionPrefix $ stepToken current token)

{- | The completions and the mask of each prefix of at most the given number
of tokens that a walk through the offered tokens reaches, the empty prefix
first. The walk steps the completions with 'stepToken' and the mask with
'maskStep'.
-}
reached ::
    (Ord symbol) =>
    Int ->
    Completions symbol ->
    Mask (Token symbol) (Term symbol) ->
    [(Completions symbol, Mask (Token symbol) (Term symbol))]
reached depth current mask =
    (current, mask)
        : concat
            [ reached (depth - 1) after maskAfter
            | depth > 0
            , (token, _) <- nextTokens current
            , Right after <- [stepToken current token]
            , Right maskAfter <- [maskStep mask token]
            ]

-- | The completions of the empty prefix of an automaton without guards.
completions :: (Ord state, Ord symbol) => Size -> FTA.FTA state symbol Constraint -> Completions symbol
completions bound = either (error . show) id . prefixCompletions bound

-- | The tokens of an automaton, and each symbol with one more child.
alphabet :: (Ord symbol) => FTA.FTA state symbol Constraint -> [Token symbol]
alphabet graph =
    nubOrd
        [ (FTA.transitionSymbol transition, arity + extra)
        | transition <- concat $ Map.elems $ FTA.transitionTable graph
        , let arity = length $ FTA.transitionChildren transition
        , extra <- [0, 1]
        ]

-- | The tokens of a term in preorder.
preorder :: Term symbol -> [(symbol, Int)]
preorder (Term.Node symbol children) = (symbol, length children) : concatMap preorder children
