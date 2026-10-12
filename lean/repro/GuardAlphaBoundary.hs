{-# LANGUAGE OverloadedStrings #-}

-- | Check that a sound incomplete solver can distinguish fresh-name spellings.
module Main (main) where

import Control.Monad (unless)
import qualified Data.CFTA.Formula as Formula
import Data.CFTA.Refinement
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import qualified Data.CFTA.Term as Term

-- | This callback proves only Top conclusions and never returns a false result.
solver :: Entailment
solver = entailmentWithBindings $ \bindings _ consequent ->
    pure $
        if consequent == Formula.Top && any ((== "__microcfta_actual_0") . fst) bindings
            then Yes
            else Unknown

-- | The last child is read for its refinement only.
guard :: Guard
guard =
    Substitute
        [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
        (Satisfies (path [4]) Formula.Top)

-- | The actuals are known distinct leaves because their annotations differ.
candidate :: Symbol -> Term.Term Symbol
candidate lastSymbol =
    Term.Node
        (RefinedSymbol "root" Formula.Top)
        [ Term.Node (RefinedSymbol "same" Formula.Top) []
        , Term.Node (RefinedSymbol "same" $ Formula.Not Formula.Bottom) []
        , Term.Node (RefinedSymbol "left" Formula.Top) []
        , Term.Node (RefinedSymbol "right" Formula.Top) []
        , Term.Node lastSymbol []
        ]

-- | Both conclusions are valid; only the solver's uncertainty changes.
main :: IO ()
main = do
    let ordinary = candidate $ RefinedSymbol "ordinary" Formula.Top
        reserved = candidate $ RefinedSymbol "__microcfta_actual_0" Formula.Top
    first <- evaluateGuard solver guard ordinary
    second <- evaluateGuard solver guard reserved
    print (first, second)
    unless (first == Yes && second == Unknown) $
        fail "Expected the source evaluator to preserve the callback's spelling-sensitive uncertainty."
    withZ3 [("__microcfta_actual_0", Formula.IntSort)] $ \z3 -> do
        ordinaryVerdict <- evaluateGuard z3 guard ordinary
        reservedVerdict <- evaluateGuard z3 guard reserved
        print (ordinaryVerdict, reservedVerdict)
        unless (ordinaryVerdict == Unknown && reservedVerdict == Yes) $
            fail "Expected the supplied solver to reject an already-declared generated name."
