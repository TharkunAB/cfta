-- | A guided search for an expression: a model prefers a sum with two different children, and the mask stops it.
module Main (main) where

import Control.Monad (forM_, unless)
import Data.List (find, sortOn)
import Data.Maybe (listToMaybe)
import Data.Ord (Down (..))
import Numeric (showFFloat)

import qualified Data.CFTA as FTA
import Data.CFTA.Gen.ExpressionLanguage (
    equalAutomaton,
    equalCompletions,
    expressionSizeBound,
    expressionText,
    structuralAutomaton,
 )
import Data.CFTA.Guided
import Data.CFTA.Guided.Model (modelScorer)
import Data.CFTA.Mask (Mask, Refusal (..), completionsMask)
import Data.CFTA.Sized.Prefix (Token, completionTerms)
import qualified Data.CFTA.Sized.Prefix.Model as Model
import Data.CFTA.Sized.Prefix.Parents (Reach (..))
import Data.CFTA.Term (Term (Node))

-- | The mask of the expressions with the equality at the empty prefix. A token is a symbol with its number of children.
equalMask :: Mask (Token Char) (Term Char)
equalMask = completionsMask equalCompletions

-- | A sum with two different children: @a+b@.
unequalSum :: Term Char
unequalSum = Node '+' [Node 'a' [], Node 'b' []]

-- | The limits of a search, without a wall-clock time.
limits :: Int -> Int -> SearchLimits
limits visits terms = SearchLimits{searchVisits = visits, searchTerms = terms, searchMicros = Nothing}

-- | The tokens of a term in preorder.
preorder :: Term Char -> [Token Char]
preorder (Node symbol children) = (symbol, length children) : concatMap preorder children

-- | A token as text.
showToken :: Token Char -> String
showToken (symbol, arity) = symbol : '/' : show arity

-- | A score with one decimal.
showScore :: Double -> String
showScore score = showFFloat (Just 1) score ""

{- | Print the found terms of a search with their scores. Each found term
must be an expression that the automaton with the equality accepts. This check
does not filter the result: the search gives only terms of the language.
-}
checked :: Guided (Token Char) (Term Char) -> IO ()
checked result = do
    forM_ (guidedTerms result) $ \(expression, score) -> do
        putStrLn $ "  " <> expressionText expression <> "  " <> showScore score
        unless (FTA.accepts equalAutomaton expression && expression /= unequalSum) $
            fail "the found term is not an expression with the equality"
    putStrLn $ "  stop: " <> show (guidedStop result)

main :: IO ()
main = do
    {- 1. A model whose most probable expression is a+b: ten expressions with
    the equality and forty copies of a+b. The context of a node has the
    parent of the node, so the model learns that b comes after + and a.
    -}
    let corpus = take 10 (completionTerms equalCompletions) <> replicate 40 unequalSum
    model <-
        maybe (fail "no model") pure $
            Model.train (Reach 1 False) structuralAutomaton (fromIntegral expressionSizeBound) corpus
    case Model.bestTerms 1 model [] of
        Just [(best, probability)] -> do
            putStrLn $ "1. The model alone writes " <> expressionText best <> ", with probability " <> showScore probability
            unless (best == unequalSum) $ fail "the model does not prefer a+b"
        other -> fail $ "unexpected best terms: " <> show other
    let scorer = modelScorer model

    -- 2. Greedy search under the mask of the expressions with the equality.
    (greedy, _) <- guide Greedy (limits 1000 1) MaskOnly scorer emptyMaskCache equalMask
    putStrLn "2. Greedy search"
    checked greedy

    -- 3. The trace: the mask changes the choice where the best score is for a token that the mask does not offer.
    putStrLn "3. The trace of the greedy search: prefix length, offered tokens, scores, choice"
    let best visit = fst <$> listToMaybe (sortOn (Down . snd) $ visitScores visit)
        changed visit = maybe False (`notElem` visitMask visit) $ best visit
        firstChanged = find changed $ guidedTrace greedy
    forM_ (guidedTrace greedy) $ \visit ->
        putStrLn $
            show (length $ visitPrefix visit)
                <> " offered "
                <> unwords (map showToken $ visitMask visit)
                <> " | scores "
                <> unwords [showToken token <> "=" <> showScore score | (token, score) <- visitScores visit]
                <> " | choice "
                <> maybe "none" showToken (visitChoice visit)
                <> if Just visit == firstChanged then "  <- the mask changes the result" else ""
    unless (fmap visitPrefix firstChanged == Just [('+', 2), ('a', 0)]) $
        fail "the mask does not change the choice after + and a"

    -- 4. Best-first search and beam search, each with a limit of three found terms.
    forM_ [BestFirst, Beam 2] $ \strategy -> do
        (found, _) <- guide strategy (limits 1000 3) MaskOnly scorer emptyMaskCache equalMask
        putStrLn $ "4. " <> show strategy
        checked found

    -- 5. The limit of visits, and a mask cache that a later search reads.
    (limited, cache) <- guide Greedy (limits 2 1) MaskOnly scorer emptyMaskCache equalMask
    unless ((guidedStop limited, null $ guidedTerms limited) == (VisitLimit, True)) $
        fail "the limit does not stop the search"
    putStrLn $
        "5. Two visits: " <> show (guidedStop limited) <> ", mask cache of " <> show (maskCacheSize cache) <> " prefixes"
    (_, cache') <- guide Greedy (limits 1000 1) MaskOnly scorer cache equalMask
    putStrLn $ "  the next search on this cache: " <> show (maskCacheSize cache') <> " prefixes"

    -- 6. Repair the tokens of an expression that a model wrote without a mask: the sum in the product has two different children.
    let written = Node '*' [unequalSum, Node 'a' []]
    (repaired, _) <- repair Greedy (limits 1000 1) MaskOnly scorer emptyMaskCache equalMask $ preorder written
    putStrLn $ "6. Repair " <> expressionText written <> ", refusal (place, reason): " <> show (repairedRefusal repaired)
    unless (repairedRefusal repaired == Just (3, TokenRejected)) $ fail "wrong place or reason"
    checked $ repairedSearch repaired
