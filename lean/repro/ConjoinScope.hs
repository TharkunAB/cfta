{-# LANGUAGE OverloadedStrings #-}

-- | Check that conjunction and intersection keep independent substitution scopes.
module Main (main) where

import Control.Monad (unless)
import qualified Data.CFTA.Formula as Formula
import Data.CFTA.Refinement
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import qualified Data.CFTA.Term as Term

-- | Bind a named integer value to one constant.
equals :: Formula.Name -> Integer -> Formula.Formula
equals name value = Formula.Atom Formula.Eq (Formula.Var name) (Formula.Lit value)

-- | A leaf with no refinement requirement.
leaf :: Symbol -> Automaton
leaf name = Node [Transition name Formula.Top [] noConstraint]

-- | Two applications share a constructor name and have different values.
actual :: Integer -> Automaton
actual value = Node [Transition "a" (equals "__cfta_value" value) [leaf "z"] noConstraint]

-- | The first independent scope proves that its actual value is zero.
first :: Guard
first = Substitute [Substitution (path [0]) (path [3])] $ Satisfies (path [5]) (equals "x" 0)

-- | The second scope cannot prove the value of the outer ambient name.
second :: Guard
second =
    Substitute [Substitution (path [2]) (path [0])]
        $ Substitute [Substitution (path [1]) (path [4])]
        $ Satisfies (path [5]) (equals "y" 1)

-- | One valid ranked automaton for each complete root guard.
graph :: Guard -> Automaton
graph guard =
    Node
        [ Transition
            "root"
            Formula.Top
            [actual 0, actual 1, leaf "b", leaf "x", leaf "y", leaf "target"]
            (semanticConstraint guard)
        ]

-- | The common term before either root guard is checked.
candidate :: Term.Term Symbol
candidate =
    let termLeaf name = Term.Node (RefinedSymbol name Formula.Top) []
        termActual value = Term.Node (RefinedSymbol "a" (equals "__cfta_value" value)) [termLeaf "z"]
     in Term.Node
            (RefinedSymbol "root" Formula.Top)
            [termActual 0, termActual 1, termLeaf "b", termLeaf "x", termLeaf "y", termLeaf "target"]

-- | The intersection must reject a term rejected by its second operand.
main :: IO ()
main = withZ3 [] $ \solver -> do
    let combined = And [first, second]
        productGraph = intersect (graph first) (graph second)
    decisions <- mapM (\guard -> evaluateGuard solver guard candidate) [first, second, combined, Substitute [] combined]
    print decisions
    accepted <- mapM (\automaton -> accepts solver automaton candidate) [graph first, graph second, productGraph]
    print accepted
    print (validate productGraph)
    unless (decisions == [Yes, No, No, No] && accepted == [Yes, No, No] && validate productGraph == Right ()) $
        fail "Conjunction changed an independent substitution scope."
