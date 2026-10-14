{-# LANGUAGE OverloadedStrings #-}

-- Run with: cabal exec -- runghc -package=cfta lean/repro/FormulaCapture.hs
module Main (main) where

import Control.Monad (unless)
import Data.CFTA.Formula
import Data.CFTA.Refinement (Verdict (..), entails)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3Assuming)

-- | Check the source substitution result and its solver interpretation.
main :: IO ()
main = do
    let original = Forall [("x", IntSort)] (Atom Eq (App "x" []) (Lit 0))
        rewritten = substitute [("unused", Var "x")] original
        expected = Forall [("__cfta_bound_1", IntSort)] (Atom Eq (Var "__cfta_bound_1") (Lit 0))
    unless (rewritten == expected) $ fail "The source substitution result changed."
    unless (null (freeNames original) && null (freeNames rewritten)) $
        fail "Substitution introduced a free name."
    withZ3Assuming [("x", IntSort)] [Atom Eq (Var "x") (Lit 0)] $ \solver -> do
        before <- entails solver Top original
        after <- entails solver Top rewritten
        unless (before == No && after == No)
            $ fail
            $ "Expected (No,No), received " <> show (before, after)
        putStrLn "Confirmed: substitution preserves the closed formula and its No verdict."
        print rewritten
