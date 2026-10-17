{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

-- | Quote a language of equal positive pairs and compile its constraints.
module Main (main) where

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, Guard (Satisfies), conjoinConstraints, equalityConstraint, semanticConstraint)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import qualified Data.CFTA.Gen.Refinement as LTA
import qualified Data.CFTA.Interned as Interned
import Data.CFTA.Path (path)
import Data.CFTA.Refinement.Expression (refinementFormula, (.==), (.>))
import Data.CFTA.Symbol (Symbol)
import qualified Data.CFTA.Symbol as Symbol
import Data.CFTA.TH (automaton)

-- | The symbol whose value is zero.
zero :: Symbol
zero = Symbol.RefinedSymbol "zero" $ refinementFormula (.== 0)

-- | The symbol whose value is one.
one :: Symbol
one = Symbol.RefinedSymbol "one" $ refinementFormula (.== 1)

-- | The children must be the same term and have a positive value.
samePositive :: Constraint
samePositive =
    conjoinConstraints
        (equalityConstraint $ mkEqConstraints [[path [0], path [1]]])
        (semanticConstraint $ Satisfies (path [0]) $ refinementFormula (.> 0))

-- | A named-state graph with symbols and constraints from Haskell bindings.
pairs :: Either (FTA.FTAError String Symbol) (FTA.PlainFTA String Symbol)
pairs =
    [automaton|
start Pair;
Pair = "pair"(Atom, Atom) where samePositive;
Atom = $zero | $one;
|]

-- | Compile once, then print the count and the accepted constructor terms.
main :: IO ()
main = do
    graph <- either (fail . show) pure pairs
    compiled <- LTA.compile $ LTA.fromAutomaton $ Interned.fromFTA graph
    print $ LTA.cardinality compiled
    print $ fmap (map Symbol.eraseRefinements) $ LTA.values compiled
