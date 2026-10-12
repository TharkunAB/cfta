{-# LANGUAGE OverloadedStrings #-}

-- | Check that requested observations preserve finite epsilon-union imports.
module Main (main) where

import Control.Monad (forM_, unless)
import qualified Data.CFTA.Gen.Refinement as Generator
import Data.CFTA.Interned (createMu, createUnion)
import Data.CFTA.Refinement
import Data.CFTA.Refinement.Expression (true)
import Data.CFTA.Refinement.Guard (requires)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import qualified Data.CFTA.Term as Term

-- | An ordinary refined leaf.
leaf :: Symbol -> Automaton
leaf name = Node [Transition name true [] noConstraint]

-- | The least fixed point has exactly the leaf a.
epsilon :: Automaton
epsilon = createMu $ \self -> createUnion [self, leaf "a"]

-- | Observe each imported root with a condition that accepts every refinement.
main :: IO ()
main = withZ3 [] $ \solver ->
    forM_ [(epsilon, ["a"]), (createUnion [epsilon, leaf "b"], ["a", "b"])] $ \(graph, names) -> do
        let expected = [Term.Node (RefinedSymbol name true) [] | name <- names]
            imported = Generator.fromAutomaton graph
            wrapped = Generator.refinedNode "wrap" (const true) (\child -> child `requires` const true) imported
        print (validate graph)
        print (Generator.values $ Generator.upToSize 1 imported)
        result <- Generator.compileWith solver wrapped
        let decoded = result >>= Generator.values
        print decoded
        unless (validate graph == Right () && decoded == Right expected) $
            fail "Requested observations dropped an imported epsilon-union term."
