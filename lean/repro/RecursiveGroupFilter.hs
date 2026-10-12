{-# LANGUAGE OverloadedStrings #-}

-- | A root-observing parent must retain the size classes of a recursive import.
module Main (main) where

import Control.Monad (forM_, unless)
import qualified Data.CFTA.Gen.Refinement as Gen
import Data.CFTA.Refinement
import Data.CFTA.Refinement.Expression (true)
import Data.CFTA.Refinement.Guard (requires)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.List (sort)

main :: IO ()
main = withZ3 [] $ \solver -> do
    let leaf name = Node [Transition name true [] noConstraint]
        productive = Mu $ \self -> Node [Transition "a" true [] noConstraint, Transition "f" true [self] noConstraint]
    forM_ [productive, createUnion [productive, leaf "b"]] $ \graph -> do
        let imported = Gen.fromAutomaton graph
            wrapped = Gen.refinedNode "wrap" (const true) (\child -> child `requires` const true) imported
        result <- Gen.compileWith solver wrapped
        case result of
            Left err -> error $ show err
            Right compiled -> do
                let counts = map (Gen.countAtSize compiled) [1 .. 5]
                    expected = Right 0 : map (Gen.countAtSize imported) [1 .. 4]
                    actualValues = fmap sort $ Gen.values $ Gen.upToSize 5 compiled
                    expectedValues = fmap sort $ Gen.values $ Gen.upToSize 4 imported
                print counts
                unless (counts == expected && actualValues == expectedValues) $
                    error "observing a recursive import lost its size-indexed language"
