{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

{- | The ranks of a term in a compiled refinement generator, by a match of the
term against the support.
-}
module Data.CFTA.Gen.CompiledRankSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Gen.Refinement (LTAGen)
import qualified Data.CFTA.Gen.Refinement as LTAGen
import Data.CFTA.Index (Cardinality (..), Rank (..), everyRank)
import Data.CFTA.Refinement.Expression (literal, true, (.&&), (.<=), (.>=))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term (Node))
import Data.String (fromString)

-- | The integers from 0 to a bound, as leaves of a term.
leaf :: Integer -> LTAGen (Term Symbol)
leaf high =
    (\n -> Node (fromString (show n)) [])
        <$> (LTAGen.every @Integer `LTAGen.satisfying` \v -> literal (0 :: Integer) .<= v .&& v .<= literal high)

-- | Sums, and differences of a larger and a smaller integer, nested up to a level.
language :: Integer -> Int -> LTAGen (Term Symbol)
language high = go
  where
    go 0 = leaf high
    go level =
        let below = go (level - 1)
         in LTAGen.oneof
                [ below
                , LTAGen.measured "add" (\_ _ -> true) (\a b -> a + b) ((\x y -> Node "add" [x, y]) <$> below <*> below)
                , LTAGen.measured "sub" (\a b -> a .>= b) (\a b -> a - b) ((\x y -> Node "sub" [x, y]) <$> below <*> below)
                ]

compiled :: Integer -> Int -> (LTAGen (Term Symbol) -> IO ()) -> IO ()
compiled high level continue = withZ3 [] $ \solver -> do
    result <- LTAGen.compileWith solver (language high level)
    either (expectationFailure . show) continue result

total :: LTAGen (Term Symbol) -> Integer
total generator = either (const 0) (\(Cardinality n) -> n) (Gen.cardinality generator)

spec :: Spec
spec = describe "ranksOfSurface" $ do
    it "gives the rank of every term of a small compiled generator" $
        compiled 3 2 $ \generator -> do
            total generator `shouldSatisfy` (> 100)
            mapM_
                ( \rank -> do
                    value <- either (fail . show) pure (Gen.unrank generator rank)
                    let ranks = either (const []) id (LTAGen.ranksOfSurface generator value)
                    ranks `shouldSatisfy` elem rank
                    -- A term in two alternatives of a choice has two ranks, and both decode to it.
                    map (Gen.unrank generator) ranks `shouldBe` map (const (Right value)) ranks
                )
                (everyRank (Cardinality (total generator)))

    it "ranks a term at early and late ranks of a million values, without listing them" $
        compiled 999999 1 $ \generator -> do
            let count = total generator
                ranks = map Rank [0, 1, 999999, 1000000, 1000001, count `div` 2, count - 1000000, count - 2, count - 1]
            mapM_
                ( \rank -> do
                    value <- either (fail . show) pure (Gen.unrank generator rank)
                    LTAGen.ranksOfSurface generator value `shouldSatisfy` either (const False) (rank `elem`)
                )
                ranks

    it "gives no rank to a term that is not in the language" $
        compiled 3 2 $ \generator -> do
            LTAGen.ranksOfSurface generator (Node "sub" [Node "1" [], Node "2" []]) `shouldBe` Right []
            LTAGen.ranksOfSurface generator (Node "7" []) `shouldBe` Right []
            LTAGen.ranksOfSurface generator (Node "mul" [Node "1" [], Node "2" []]) `shouldBe` Right []
            LTAGen.ranksOfSurface generator (Node "add" [Node "1" []]) `shouldBe` Right []
