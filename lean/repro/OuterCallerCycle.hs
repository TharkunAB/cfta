{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (unless)
import Data.CFTA.Equality
import qualified Data.Set as Set
import System.Environment (getArgs)
import System.IO (BufferMode (LineBuffering), hSetBuffering, stdout)
import System.Timeout (timeout)

-- | Put one unconstrained ordinary wrapper above a node.
wrap :: Node String -> Node String
wrap value = Node [Edge "w" [value]]

-- | Check the exact two-call dependency cycle, or demand the pass in a fresh process.
main :: IO ()
main = do
    hSetBuffering stdout LineBuffering
    arguments <- getArgs
    let same = mkEqConstraints [[path [0], path [1]]]
        plain = Mu $ \r -> Node [Edge "a" [], Edge "p" [wrap r, wrap r]]
        next = Node [Edge "p" [wrap plain, wrap plain]]
        constrained = Mu $ \r -> Node [Edge "a" [], mkEdge "p" [wrap r, wrap next] (equalityConstraint same)]
        rootEdge = mkEdge "p" [wrap constrained, wrap next] (equalityConstraint same)
        root = Node [rootEdge]
        narrowed = reduceEdgeIntersection EmptyConstraints rootEdge
        checked =
            all (Set.null . freeVars) [plain, next, constrained, root]
                && intersect constrained plain == constrained
                && intersect next plain == next
                && intersect constrained next == root
                && edgeChildren narrowed == [wrap root, wrap root]
                && combineEqConstraints EmptyConstraints (equalities (edgeConstraint narrowed)) == same
                && eqConstraintsDescend same 0 == EmptyConstraints
                && eqConstraintsDescend same 1 == EmptyConstraints
    case arguments of
        ["--cold"] -> do
            result <- timeout 3000000 (evaluate (nodeIdentity (reducePartially root)))
            print result
        [] -> do
            result <- timeout 3000000 (evaluate checked)
            print result
            unless (result == Just True) (fail "outer caller cycle certificate")
            outcome <- timeout 3000000 (evaluate (nodeIdentity (reducePartially root)))
            print outcome
        _ -> fail "usage: OuterCallerCycle [--cold]"
