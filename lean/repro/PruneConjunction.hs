{-# LANGUAGE OverloadedStrings #-}

-- | Check convergence when equality narrowing combines different residual guards.
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import Data.CFTA.Constraint (equalityConstraint)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Refinement
import Data.CFTA.Refinement.Expression (true)
import qualified Data.CFTA.Term as Term
import System.Timeout (timeout)

-- | A leaf with a residual guard.
atom :: Guard -> Automaton
atom guard = Node [Transition "a" true [] (semanticConstraint guard)]

-- | This guard accepts the current term.
reflexive :: Guard
reflexive = Same (path []) (path [])

-- | These guards have different syntax and accept the same leaf.
inputs :: [Automaton]
inputs = map atom [reflexive, And [reflexive, reflexive], Or [reflexive, reflexive]]

-- | All three positions must contain the same term.
original :: Automaton
original = Node [Transition "triple" true inputs (equalityConstraint (mkEqConstraints [[path [0], path [1], path [2]]]))]

-- | The guards do not require solver queries.
solver :: Entailment
solver = Entailment $ \_ _ -> pure Yes

-- | Count the constructors that grew in each historical narrowing pass.
guardSize :: Guard -> Int
guardSize (And guards) = 1 + sum (map guardSize guards)
guardSize (Or guards) = 1 + sum (map guardSize guards)
guardSize (Not guard) = 1 + guardSize guard
guardSize _ = 1

-- | Count the residual guard constructors at each root.
sizes :: [Automaton] -> [Int]
sizes = map (sum . map (guardSize . constraintGuard . edgeConstraint) . nodeEdges)

-- | Use the operand order in the equality reduction helper.
intersections :: [Automaton] -> Automaton
intersections [] = EmptyNode
intersections (first : rest) = foldr intersect first rest

-- | Narrow each root by the other two roots.
oneEqualityPass :: [Automaton] -> [Automaton]
oneEqualityPass nodes = [intersect (intersections [other | (j, other) <- indexed, j /= i]) node | (i, node) <- indexed]
  where
    indexed = zip [0 :: Int ..] nodes

-- | Check membership, guard convergence, and completion of the pruning fixpoint.
main :: IO ()
main = do
    print (validate original)
    let a = Term.Node (RefinedSymbol "a" true) []
        term = Term.Node (RefinedSymbol "triple" true) [a, a, a]
    accepts solver original term >>= print
    forM_ (zip [0 :: Int ..] (take 7 (iterate oneEqualityPass inputs))) $ \(iteration, nodes) ->
        print (iteration, map nodeIdentity nodes, sizes nodes)
    result <- timeout 2000000 $ do
        pruned <- prune solver original
        case pruned of
            Left failure -> evaluate (length (show failure)) >> pure "error"
            Right EmptyNode -> pure "empty"
            Right node -> do
                evaluate (nodeIdentity node)
                verdict <- accepts solver node term
                if verdict == Yes then pure "finished" else error "Pruning lost the accepted term."
    print result
    if result == Just "finished" then pure () else error "Pruning did not finish."
