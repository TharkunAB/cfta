{-# LANGUAGE OverloadedStrings #-}

-- | Compare repeated open keys and different coordinate widths with finite pools.
module Main (main) where

import Control.Monad (forM_, unless)
import Data.List (sort)
import qualified Data.Map.Strict as Map

import qualified Data.CFTA.Gen.Refinement.QuickCheck as Gen
import Data.CFTA.Index (everyRank)
import Data.CFTA.Ranked.Internal.Sampler (Exact (..))
import Data.CFTA.Refinement.Expression (literal, true, (.&&), (.<=))
import Data.CFTA.Refinement.Lattice (latticeEntailment)

-- | The symbolic source leaves one coordinate open until its parent closes it.
symbolic :: Integer -> Integer -> Gen.LTAGen Integer
symbolic low high = Gen.every `Gen.satisfying` (\value -> literal low .<= value .&& value .<= literal high)

-- | The finite reference enumerates the same integer values.
listed :: Integer -> Integer -> Gen.LTAGen Integer
listed low high = Gen.elements [low .. high]

-- | Equal root keys can carry different decoded values; another branch has two coordinates.
recipe :: (Integer -> Integer -> Gen.LTAGen Integer) -> Bool -> Int -> Maybe Integer -> Gen.LTAGen Integer
recipe source uniform payments bound = parent $ iterate Gen.pay selected !! payments
  where
    one = Gen.measured "measure" (const true) id $ source 0 2
    two = Gen.measured "measure" (\_ _ -> true) (+) $ (+) <$> source 0 2 <*> source 1 2
    three =
        Gen.measured "measure" (\_ _ _ -> true) (\a b c -> a + b + c) $
            (\a b c -> a + b + c) <$> source 0 1 <*> source 0 1 <*> source 1 2
    alternatives = [one, (+ 10) <$> one, two, three]
    selected
        | uniform = Gen.uniformly alternatives
        | otherwise = Gen.frequency $ zip [1, 3, 2, 4] alternatives
    parent = case bound of
        Nothing -> Gen.node "parent"
        Just limit -> Gen.guarded "parent" (\value -> value .<= literal limit)

-- | Keep every exact sampler contribution, including repeated decoded values.
sampled :: Gen.LTAGen Integer -> [(Integer, Rational)]
sampled generator = Map.toAscList $ Map.fromListWith (+) [(value, mass) | (mass, Right value) <- runExact $ Gen.lowerVia generator]

-- | Check complete rank preimages as well as counts and global and bounded distributions.
check :: (Bool, Int, Maybe Integer) -> IO Int
check description@(uniform, payments, bound) = do
    compiled <- either (error . show) pure =<< Gen.compileWith latticeEntailment (recipe symbolic uniform payments bound)
    reference <- either (error . show) pure =<< Gen.compileWith latticeEntailment (recipe listed uniform payments bound)
    unless (Gen.cardinality compiled == Gen.cardinality reference && Gen.pmf compiled == Gen.pmf reference)
        $ error
        $ "count or mass differs: " <> show description <> " " <> show (Gen.pmf compiled, Gen.pmf reference)
    count <- either (error . show) pure $ Gen.cardinality compiled
    terms <- traverse (either (error . show) pure . Gen.termAt compiled) $ everyRank count
    let ranksByTerm = Map.fromListWith (<>) [(term, [rank]) | (rank, term) <- zip (everyRank count) terms]
    forM_ (Map.toList ranksByTerm) $ \(term, expected) -> do
        actual <- either (error . show) pure $ Gen.ranksOf compiled term
        unless (sort actual == sort expected)
            $ error
            $ "complete inverse rank set differs: " <> show description <> " " <> show (actual, expected)
    forM_ [0 .. 10] $ \size -> do
        let actual = Gen.upToSize size compiled
            expected = Gen.upToSize size reference
        unless
            ( Gen.countAtSize compiled size == Gen.countAtSize reference size
                && Gen.pmf actual == Gen.pmf expected
                && sampled actual == sampled expected
            )
            $ error
            $ "bounded count or exact distribution differs: " <> show (description, size)
    pure $ length terms

main :: IO ()
main = do
    let cases = [(uniform, payments, bound) | uniform <- [False, True], payments <- [0, 1], bound <- [Nothing, Just 1, Just 3]]
    counts <- traverse check cases
    putStrLn $
        show (length cases)
            <> " heterogeneous open-group cases; "
            <> show (sum counts)
            <> " complete rank preimages; global and bounded counts, PMFs, and exact samplers agree."
