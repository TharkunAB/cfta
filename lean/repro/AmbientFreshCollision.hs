{-# LANGUAGE OverloadedStrings #-}

-- The former adapter returned (Yes, No) for the first two queries.
-- An undeclared ambient name captured the first supposedly fresh value.
-- The repaired adapter rejects that collision with Unknown.
import Control.Monad (unless)
import Data.CFTA.Formula (Formula (..), Relation (..), Sort (..), Term (..))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3Assuming)
import Data.CFTA.Refinement.Verdict (Verdict (..), entails, entailsWithBindings)

-- | Check ambient freshness and preserve implicit and quantified declarations.
main :: IO ()
main = do
    collisionResults <-
        withZ3Assuming [] [Atom Eq (Var "__cfta_actual_0") (Lit 0)] $ \solver -> do
            collision <-
                entailsWithBindings solver [("__cfta_actual_0", "actual")] Top $
                    Atom Eq (Var "__cfta_actual_0") (Lit 0)
            independent <-
                entailsWithBindings solver [("__cfta_actual_1", "actual")] Top $
                    Atom Eq (Var "__cfta_actual_1") (Lit 0)
            ambient <- entails solver Top $ Atom Eq (Var "__cfta_actual_0") (Lit 0)
            pure (collision, independent, ambient)
    boundName <-
        withZ3Assuming [] [Forall [("fresh", IntSort)] (Atom Eq (Var "fresh") (Var "fresh"))] $ \solver ->
            entailsWithBindings solver [("fresh", "actual")] Top $ Atom Eq (Var "fresh") (Lit 0)
    print collisionResults
    print boundName
    unless (collisionResults == (Unknown, No, Yes) && boundName == No) $
        fail "ambient freshness result changed"
