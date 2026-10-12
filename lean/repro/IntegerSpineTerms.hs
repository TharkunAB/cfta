{-# LANGUAGE OverloadedStrings #-}

-- | Check the private keyed terms of the generated open integer spine.
module Main (main) where

import Control.Monad (forM_, unless)
import Data.String (fromString)

import Data.CFTA.Gen.Label (Label (..))
import qualified Data.CFTA.Gen.Refinement as Gen
import Data.CFTA.Index (everyRank)
import Data.CFTA.Refinement (Symbol (RefinedSymbol))
import Data.CFTA.Refinement.Expression (literal, refinementFormula, (.&&), (.<=), (.==))
import Data.CFTA.Refinement.Lattice (latticeEntailment)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | The private constructor used by pairBucket for its only retained pair.
paired :: Term (Label Symbol) -> Term (Label Symbol) -> Term (Label Symbol)
paired left right =
    Term.Node
        JoinN
        [ Term.Node CenterKeyed [Term.Node Pure [], first, second]
        , Term.Node ArgKeyed [first, left]
        , Term.Node ArgKeyed [second, right]
        ]
  where
    first = Term.Node (ArgKey 0 0) []
    second = Term.Node (ArgKey 0 1) []

-- | The actual integerSymbol refinement, including the complete singleton formula.
integer :: Integer -> Term (Label Symbol)
integer value = Term.Node (Label $ RefinedSymbol (fromString $ show value) $ refinementFormula (.== literal value)) []

-- | Compare every selected term and inverse rank with the source constructor projection.
check :: String -> Gen.LTAGen a -> (a -> Term (Label Symbol)) -> IO ()
check name recipe expected = do
    compiled <- either (error . show) pure =<< Gen.compileWith latticeEntailment recipe
    count <- either (error . show) pure $ Gen.cardinality compiled
    forM_ (everyRank count) $ \rank -> do
        value <- either (error . show) pure $ Gen.unrank compiled rank
        term <- either (error . show) pure $ Gen.termAt compiled rank
        unless (term == expected value && Gen.rankOf compiled term == Right rank)
            $ error
            $ name <> ": private compiler term or inverse rank differs at " <> show rank <> "\n" <> show term
    putStrLn $ name <> ": " <> show count <> " exact keyed terms and inverse ranks"

main :: IO ()
main = do
    let digit = Gen.every `Gen.satisfying` (\v -> 0 .<= v .&& v .<= 2) :: Gen.LTAGen Integer
        pureTerm = Term.Node Pure []
    check "mapped pair" ((,) <$> digit <*> digit) $ \(left, right) -> paired (integer left) (integer right)
    check "nested lifted pair" (pure (,) <*> digit <*> digit) $ \(left, right) -> paired (paired pureTerm $ integer left) (integer right)
    check "nested identity" (pure id <*> (pure id <*> digit)) $ \value -> paired pureTerm (paired pureTerm $ integer value)
    check "mapped integer" ((+ 1) <$> digit) $ integer . subtract 1
