{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.DefinitionSpec (spec) where

import qualified Data.Map.Strict as Map
import Data.String (fromString)
import Test.Hspec

import Data.CFTA.Formula (Formula (..), Relation (..), Sort (..), Term (..))
import Data.CFTA.Refinement (Entailment (entails), RefinementRelation (..), Verdict (..), refinementRelation)
import Data.CFTA.Refinement.Definition (Definition (..), DefinitionError (..), Definitions, unfold, unfoldKeeping)
import Data.CFTA.Refinement.Expression (predicate, refinementFormula, (.==))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3Definitions)
import Data.CFTA.Symbol (valueName)

-- | @between x lo hi@, @digit d@, and definitions for the error cases.
definitions :: Definitions
definitions =
    Map.fromList
        [
            ( "between"
            , Definition
                [("x", IntSort), ("lo", IntSort), ("hi", IntSort)]
                (And [Atom Le (Var "lo") (Var "x"), Atom Le (Var "x") (Var "hi")])
            )
        , ("digit", Definition [("d", IntSort)] (Predicate "between" [Var "d", Lit 0, Lit 9]))
        , ("hasSuccessor", Definition [("x", IntSort)] (Exists [("y", IntSort)] (Atom Eq (Var "y") (Add (Var "x") (Lit 1)))))
        , ("ignoresArgument", Definition [("x", IntSort)] Top)
        , ("belowLimit", Definition [("x", IntSort)] (Atom Lt (Var "x") (Var "limit")))
        , ("twice", Definition [("x", IntSort), ("x", IntSort)] Top)
        , ("ping", Definition [("x", IntSort)] (Predicate "pong" [Var "x"]))
        , ("pong", Definition [("x", IntSort)] (Predicate "ping" [Var "x"]))
        ]

spec :: Spec
spec = do
    describe "unfold" $ do
        it "puts the arguments in place of the parameters" $
            unfold definitions [] (Predicate "between" [Var "v", Lit 0, Lit 3])
                `shouldBe` Right (And [Atom Le (Lit 0) (Var "v"), Atom Le (Var "v") (Lit 3)])

        it "unfolds a definition that uses another definition" $
            unfold definitions [] (Predicate "digit" [Var "v"])
                `shouldBe` Right (And [Atom Le (Lit 0) (Var "v"), Atom Le (Var "v") (Lit 9)])

        it "renames a bound name that an argument would capture" $
            case unfold definitions [] (Predicate "hasSuccessor" [Var "y"]) of
                Right (Exists [(bound, IntSort)] (Atom Eq (Var use) (Add (Var "y") (Lit 1)))) -> do
                    use `shouldBe` bound
                    bound `shouldNotBe` "y"
                other -> expectationFailure $ "unexpected unfolding: " <> show other

        it "keeps a formula without predicates" $
            unfold definitions [] (Atom Gt (Var "v") (Lit 0)) `shouldBe` Right (Atom Gt (Var "v") (Lit 0))

        it "rejects an undefined predicate" $
            unfold definitions [] (Predicate "missing" [Var "v"]) `shouldBe` Left (UndefinedPredicate "missing")

        it "rejects the wrong number of arguments" $
            unfold definitions [] (Predicate "between" [Var "v", Lit 0]) `shouldBe` Left (ArityMismatch "between" 3 2)

        it "checks an argument that the body does not use" $
            unfold definitions [("flag", BoolSort)] (Predicate "ignoresArgument" [Var "flag"])
                `shouldBe` Left (ArgumentSort "ignoresArgument" 0 IntSort BoolSort)

        it "rejects an ordering on booleans" $
            unfold definitions [("flag", BoolSort)] (Atom Lt (Var "flag") (Lit 1))
                `shouldBe` Left (IllSortedAtom Lt (Var "flag") (Lit 1))

        it "rejects a free name in a body" $
            unfold definitions [] (Predicate "belowLimit" [Var "v"]) `shouldBe` Left (FreeName "belowLimit" "limit")

        it "rejects a parameter list that names a value twice" $
            unfold definitions [] (Predicate "twice" [Lit 0, Lit 1]) `shouldBe` Left (DuplicateBinder "x")

        it "rejects definitions that use each other" $
            unfold definitions [] (Predicate "ping" [Var "v"]) `shouldBe` Left (DefinitionCycle "ping")

    describe "unfoldKeeping" $ do
        let list = NamedSort "List" [IntSort]
            kept = Map.fromList [("sorted", [list])]

        it "keeps a predicate of the signatures in place" $
            unfoldKeeping kept definitions [("v", list)] (And [Predicate "sorted" [Var "v"], Predicate "digit" [Lit 3]])
                `shouldBe` Right (And [Predicate "sorted" [Var "v"], And [Atom Le (Lit 0) (Lit 3), Atom Le (Lit 3) (Lit 9)]])

        it "checks the arguments of a kept predicate" $
            unfoldKeeping kept definitions [] (Predicate "sorted" [Var "v"]) `shouldBe` Left (ArgumentSort "sorted" 0 list IntSort)

        it "unfolds a definition before a signature of the same name" $
            unfoldKeeping
                (Map.fromList [("between", [IntSort, IntSort, IntSort])])
                definitions
                []
                (Predicate "between" [Var "v", Lit 0, Lit 3])
                `shouldBe` Right (And [Atom Le (Lit 0) (Var "v"), Atom Le (Var "v") (Lit 3)])

    describe "withZ3Definitions" $ do
        let value = fromString valueName
            between lo hi = refinementFormula (\v -> predicate "between" [v, lo, hi])
            digit = refinementFormula (\v -> predicate "digit" [v])

        it "decides a defined predicate exactly" $
            withZ3Definitions definitions [(value, IntSort)] [] $ \solver -> do
                entails solver (refinementFormula (.== 2)) (between 0 3) >>= (`shouldBe` Yes)
                entails solver (refinementFormula (.== 5)) (between 0 3) >>= (`shouldBe` No)

        it "compares refinements through their definitions" $
            withZ3Definitions definitions [(value, IntSort)] [] $ \solver ->
                refinementRelation solver digit (between 0 10) >>= (`shouldBe` StrictSubtype)

        it "gives Unknown for a predicate without a definition" $
            withZ3Definitions definitions [(value, IntSort)] [] $ \solver ->
                entails solver Top (refinementFormula (\v -> predicate "missing" [v])) >>= (`shouldBe` Unknown)
