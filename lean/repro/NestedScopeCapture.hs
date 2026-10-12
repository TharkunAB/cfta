{-# LANGUAGE OverloadedStrings #-}

-- | Compare sparse and complete identity scopes through nested substitution.
module Main (main) where

import Control.Monad (unless)
import qualified Data.CFTA.Formula as Formula
import Data.CFTA.Path (getPath)
import Data.CFTA.Refinement
import Data.CFTA.Refinement.Evaluate (Observed (..), evaluateGuardWithShape, leafnessOf)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import qualified Data.CFTA.Term as Term

-- | Both inner actuals have this refinement and the same complete subtree.
zero :: Formula.Formula
zero = Formula.Atom Formula.Eq (Formula.Var "__microcfta_value") (Formula.Lit 0)

-- | The outer scope replaces the ambient name used by the complete inner actual.
guard :: Guard
guard =
    Substitute [Substitution (path [2]) (path [0])]
        $ Substitute [Substitution (path [0]) (path [3]), Substitution (path [1]) (path [4])]
        $ Satisfies (path [5]) (Formula.Atom Formula.Eq (Formula.Var "x") (Formula.Lit 0))

-- | This grammar has one underlying term before its root guard is checked.
grammar :: Automaton
grammar =
    let leaf name = Node [Transition name Formula.Top [] noConstraint]
        actual = Node [Transition "a" zero [leaf "z"] noConstraint]
     in Node
            [Transition "root" Formula.Top [actual, actual, leaf "b", leaf "x", leaf "y", leaf "target"] (semanticConstraint guard)]

-- | The source complete term has two equal inner actuals.
candidate :: Term.Term Symbol
candidate =
    let leaf name = Term.Node (RefinedSymbol name Formula.Top) []
        actual = Term.Node (RefinedSymbol "a" zero) [leaf "z"]
     in Term.Node (RefinedSymbol "root" Formula.Top) [actual, actual, leaf "b", leaf "x", leaf "y", leaf "target"]

-- | Print the guard pair and the original/pruned language membership pair.
main :: IO ()
main = withZ3 [] $ \solver -> do
    let observed target = do
            Term.Node symbol children <- getPath target candidate
            pure $ Observed symbol (leafnessOf children)
    complete <- evaluateGuard solver guard candidate
    sparse <- evaluateGuardWithShape solver observed guard
    print (complete, sparse)
    original <- accepts solver grammar candidate
    result <- prune solver grammar
    case result of
        Left err -> fail $ show err
        Right pruned -> do
            rewritten <- accepts solver pruned candidate
            print (original, rewritten)
            unless (original == rewritten) $
                fail "Pruning changed acceptance of the nested-substitution term."
