{-# LANGUAGE OverloadedStrings #-}

-- The former adapter returned (Yes, No). Liquid Fixpoint serialized "1"
-- and "fix$1" to the same SMT name. The binder captured the free variable.
-- The repaired adapter keeps both names distinct and returns (No, No).
import Control.Monad (unless)
import Data.CFTA.Formula (Formula (..), Relation (..), Sort (..), Term (..))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.CFTA.Refinement.Verdict (Verdict (..), entails)

-- | Check distinct SMT names across declarations, binders, and variables.
main :: IO ()
main = do
    collision <- withZ3 [("1", IntSort)] $ \solver ->
        entails solver Top $
            Forall [("fix$1", IntSort)] (Atom Eq (Var "1") (Var "fix$1"))
    independent <- withZ3 [("1", IntSort)] $ \solver ->
        entails solver Top $
            Forall [("independent", IntSort)] (Atom Eq (Var "1") (Var "independent"))
    shared <- withZ3 [("1", IntSort), ("fix$1", IntSort)] $ \solver ->
        entails solver (Atom Eq (Var "1") (Lit 0)) (Atom Eq (Var "fix$1") (Lit 0))
    identity <- withZ3 [] $ \solver ->
        entails solver Top $
            Forall [("1", IntSort)] (Atom Eq (Var "1") (Var "1"))
    print (collision, independent, shared, identity)
    unless ((collision, independent, shared, identity) == (No, No, No, Yes)) $
        fail "SMT name encoding changed formula meaning"
