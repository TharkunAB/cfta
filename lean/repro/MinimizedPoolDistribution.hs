{-# LANGUAGE OverloadedStrings #-}

-- | Pool minimization retains entries and starts a new uniform distribution.
module Main (main) where

import Control.Monad (unless)
import qualified Data.CFTA.Gen.Refinement as Gen
import Data.CFTA.Refinement.Expression (true)
import Data.CFTA.Refinement.Lattice (latticeEntailment)
import Data.Ratio ((%))

main :: IO ()
main = do
    let entries =
            [ Gen.Refined (0 :: Integer) "a" (const true)
            , Gen.Refined 1 "b" (const true)
            , Gen.Refined 2 "c" (const true)
            ]
        representative value = if value < 2 then 0 else 2
        original = Gen.namedPool entries
    minimized <- either (error . show) pure =<< Gen.minimizePoolOn latticeEntailment (< 2) entries
    unless (Gen.values minimized == Right [0, 2]) $
        error "the retained representatives differ"
    unless (Gen.pmf minimized == Right [(0, 1 % 2), (2, 1 % 2)]) $
        error "the retained pool distribution differs"
    unless (Gen.pmf (representative <$> original) == Right [(0, 2 % 3), (2, 1 % 3)]) $
        error "the original class masses differ"
    putStrLn "Minimized representatives have masses 1/2 and 1/2; original class masses are 2/3 and 1/3."
