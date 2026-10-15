{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (unless)
import Data.CFTA.Equality
import Data.Monoid (Sum (..))
import qualified Data.Set as Set
import System.Timeout (timeout)

-- | Count ordinary nodes, all physical nodes, and edges in the stored graph.
counts :: Node String -> (Int, Int, Int)
counts value = (nodeCount value, getSum (crush (const (Sum 1)) value), edgeCount value)

-- | Check two physical changes under repeated intersection with one fixed input.
main :: IO ()
main = do
    let first = Mu $ \x -> Node [Edge "a" [], Edge "u" [x], Edge "u" [Node [Edge "u" [x]]]]
        original = Mu $ \x -> Node [Edge "a" [], Edge "u" [Node [Edge "u" [x]]]]
        once = intersect original first
        twice = intersect once first
        same = equalityConstraint (mkEqConstraints [[path [0], path [1]]])
        narrowed left = reduceEdgeIntersection EmptyConstraints (mkEdge "root" [left, first] same)
        actualFirst = case edgeChildren (narrowed original) of
            child : _ -> child == once
            [] -> False
        actualSecond = case edgeChildren (narrowed once) of
            child : _ -> child == twice
            [] -> False
        observed = map counts [original, once, twice]
        checked =
            observed == [(2, 3, 3), (4, 6, 7), (12, 19, 26)]
                && original /= once
                && once /= twice
                && all (Set.null . freeVars) [first, original, once, twice]
                && actualFirst
                && actualSecond
    result <- timeout 10000000 (evaluate checked)
    print result
    unless (result == Just True) (fail "two-step physical intersection growth")
    print observed
    print (map nodeIdentity [original, once, twice])
