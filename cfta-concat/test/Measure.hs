{- | The precondition of @head@ with the uninterpreted measure 'len'.

The same Haskell text is the formula, with @len@ as an uninterpreted function
of the logic, and the predicate on values, with 'length'.
-}
module Main (main) where

import Control.Monad (unless)

import Data.CFTA.Refinement.Expression (Formula, uninterpreted, variable, (.>=))

import ConCat.Rebox ()
import Data.CFTA.Concat (len, symbolic)

-- | The precondition of @head@: the list is not empty.
nonEmpty :: [Integer] -> Bool
nonEmpty xs = len xs >= 1
{-# INLINE nonEmpty #-}

-- | The formula of the precondition, about a list named @xs@.
compiled :: Formula
compiled = symbolic nonEmpty (variable "xs")

-- | The formula with the uninterpreted measure @len@.
expected :: Formula
expected = uninterpreted "len" [variable "xs"] .>= 1

main :: IO ()
main = do
    print compiled
    unless (compiled == expected && show compiled == show expected)
        $ fail
        $ "expected " <> show expected
    unless (map nonEmpty [[], [1], [1, 2]] == [False, True, True]) $
        fail "nonEmpty on values"
    putStrLn "measure: all checks pass"
