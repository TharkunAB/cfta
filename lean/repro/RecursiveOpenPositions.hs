{-# LANGUAGE OverloadedStrings #-}

-- | Recursive open groups must report their supported error without a partial lookup.
module Main (main) where

import Control.Monad (forM_, unless)
import qualified Data.CFTA.Gen.Refinement as Gen
import Data.CFTA.Refinement
import Data.CFTA.Refinement.Expression
import Data.CFTA.Refinement.Lattice (latticeEntailment)

main :: IO ()
main = do
    let graph = Mu $ \self -> Node [Transition "a" true [] noConstraint, Transition "f" true [self] noConstraint]
        recursive = const (0 :: Integer) <$> Gen.fromAutomaton graph
        digits = Gen.every `Gen.satisfying` (\v -> 1 .<= v .&& v .<= 2)
        applied = (+) <$> recursive <*> digits
        choices =
            [ Gen.uniformly [recursive, digits]
            , Gen.oneof [recursive, digits]
            , Gen.uniformly [applied, digits]
            , Gen.oneof [applied, digits]
            ]
    forM_ choices $ \choice -> do
        result <- Gen.compileWith latticeEntailment $ Gen.node "p" choice
        unless (fmap Gen.cardinality result == Right (Left Gen.UnboundedGenerator)) $
            error "recursive open groups changed their explicit error"
    putStrLn "All four recursive open choices return UnboundedGenerator without a partial lookup."
