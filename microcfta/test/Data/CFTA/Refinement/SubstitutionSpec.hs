{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.SubstitutionSpec (spec) where

import Data.CFTA.Formula (Formula (Forall), Name, Sort (..))
import qualified Data.CFTA.Formula as Formula
import Data.CFTA.Refinement (
    Constraint,
    Entailment (Entailment),
    Guard (Satisfies, Substitute),
    Substitution (Substitution),
    Symbol (RefinedSymbol),
    Verdict (..),
    entails,
    evaluateConstraint,
    evaluateGuard,
    path,
 )
import Data.CFTA.Refinement.Expression (false, true, variable, (.<), (.==))
import Data.CFTA.Refinement.Guard (buildGuard, isSubtypeOf, withActualFor, withActualsFor)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3, withZ3Assuming)
import Data.CFTA.Symbol (valueName)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term
import Data.String (fromString)
import Test.Hspec (Spec, describe, it, shouldBe)

equalityEntailment :: Entailment
equalityEntailment = Entailment $ \antecedent consequent ->
    pure $ if antecedent == consequent then Yes else No

dependentGuard :: Constraint
dependentGuard =
    buildGuard $ \resultType functionOutput actual formal ->
        withActualFor actual formal $
            functionOutput `isSubtypeOf` resultType

spec :: Spec
spec =
    describe "dependent LTA guards" $ do
        describe "formula substitution" $ do
            it "renames a bound nullary application without introducing a free name" $ do
                let original = Formula.Forall [("x", IntSort)] $ Formula.Atom Formula.Eq (Formula.App "x" []) (Formula.Lit 0)
                    rewritten = Formula.substitute [("unused", Formula.Var "x")] original
                    expected =
                        Formula.Forall [("__microcfta_bound_1", IntSort)] $
                            Formula.Atom Formula.Eq (Formula.Var "__microcfta_bound_1") (Formula.Lit 0)
                rewritten `shouldBe` expected
                Formula.freeNames rewritten `shouldBe` []
                withZ3Assuming [("x", IntSort)] [Formula.Atom Formula.Eq (Formula.Var "x") (Formula.Lit 0)] $ \solver -> do
                    entails solver true original >>= (`shouldBe` No)
                    entails solver true rewritten >>= (`shouldBe` No)

            it "substitutes a nullary application as a named value" $ do
                Formula.substitute [("x", Formula.Lit 4)] (Formula.Atom Formula.Eq (Formula.App "x" []) (Formula.Var "x"))
                    `shouldBe` Formula.Atom Formula.Eq (Formula.Lit 4) (Formula.Lit 4)

            it "renames a function head and substitutes its arguments simultaneously" $ do
                Formula.substitute
                    [("f", Formula.Var "g"), ("g", Formula.Var "h"), ("x", Formula.Lit 4)]
                    (Formula.Atom Formula.Eq (Formula.App "f" [Formula.Var "x"]) (Formula.App "g" [Formula.Var "x"]))
                    `shouldBe` Formula.Atom Formula.Eq (Formula.App "g" [Formula.Lit 4]) (Formula.App "h" [Formula.Lit 4])

            it "reports a replacement that the named function syntax cannot apply" $ do
                Formula.substituteChecked
                    [("f", Formula.Lit 4)]
                    (Formula.Atom Formula.Eq (Formula.App "f" [Formula.Lit 0]) (Formula.Lit 0))
                    `shouldBe` Left (Formula.UnsupportedFunctionReplacement "f" $ Formula.Lit 4)

            it "leaves the applications of a function name whose replacement is not a name" $
                Formula.substitute
                    [("f", Formula.Lit 4), ("x", Formula.Lit 1)]
                    (Formula.Atom Formula.Eq (Formula.App "f" [Formula.Var "x"]) (Formula.Lit 0))
                    `shouldBe` Formula.Atom Formula.Eq (Formula.App "f" [Formula.Lit 1]) (Formula.Lit 0)

            it "ignores an unsupported replacement where a function binder shadows it" $ do
                let original =
                        Formula.Forall [("f", FunctionSort [IntSort] IntSort)] $
                            Formula.Atom Formula.Eq (Formula.App "f" [Formula.Lit 0]) (Formula.Lit 0)
                Formula.substituteChecked [("f", Formula.Lit 4)] original `shouldBe` Right original

            it "renames a captured bound function at each application head" $ do
                let original =
                        Formula.Forall [("f", FunctionSort [IntSort] IntSort)] $
                            Formula.Atom Formula.Eq (Formula.App "f" [Formula.Lit 0]) (Formula.App "g" [Formula.Lit 0])
                    expected =
                        Formula.Forall [("__microcfta_bound_1", FunctionSort [IntSort] IntSort)] $
                            Formula.Atom Formula.Eq (Formula.App "__microcfta_bound_1" [Formula.Lit 0]) (Formula.App "f" [Formula.Lit 0])
                Formula.substitute [("g", Formula.Var "f")] original `shouldBe` expected

            it "keeps the last of repeated binders effective after renaming" $ do
                let original = Formula.Forall [("x", IntSort), ("x", IntSort)] $ Formula.Atom Formula.Eq (Formula.Var "x") (Formula.Lit 0)
                    expected =
                        Formula.Forall [("__microcfta_bound_1", IntSort), ("__microcfta_bound_1", IntSort)] $
                            Formula.Atom Formula.Eq (Formula.Var "__microcfta_bound_1") (Formula.Lit 0)
                Formula.substitute [("unused", Formula.Var "x")] original `shouldBe` expected

            it "keeps the first nonidentity replacement for a duplicate name" $ do
                Formula.substitute
                    [("x", Formula.Var "x"), ("x", Formula.Lit 1), ("x", Formula.Lit 2)]
                    (Formula.Atom Formula.Eq (Formula.App "x" []) (Formula.Var "x"))
                    `shouldBe` Formula.Atom Formula.Eq (Formula.Lit 1) (Formula.Lit 1)

        it "substitutes the actual argument for the formal in the result type" $ do
            let expected = variable valueName .== variable "x"
                dependent = variable valueName .== variable "n"
                term =
                    Term.Node
                        ( RefinedSymbol
                            "app"
                            true
                        )
                        [ Term.Node (RefinedSymbol "result" expected) []
                        , Term.Node (RefinedSymbol "output" dependent) []
                        , Term.Node (RefinedSymbol "x" true) []
                        , Term.Node (RefinedSymbol "n" true) []
                        ]
            evaluateConstraint equalityEntailment dependentGuard term >>= (`shouldBe` Yes)

        it "keeps different actual arguments distinct" $ do
            let expected = variable valueName .== variable "y"
                dependent = variable valueName .== variable "n"
                term =
                    Term.Node
                        ( RefinedSymbol
                            "app"
                            true
                        )
                        [ Term.Node (RefinedSymbol "result" expected) []
                        , Term.Node (RefinedSymbol "output" dependent) []
                        , Term.Node (RefinedSymbol "x" true) []
                        , Term.Node (RefinedSymbol "n" true) []
                        ]
            evaluateConstraint equalityEntailment dependentGuard term >>= (`shouldBe` No)

        it "substitutes several actual arguments in one dependent result" $ do
            let expected = variable valueName .== variable "x" + variable "y"
                dependent = variable valueName .== variable "n" + variable "m"
                guard =
                    buildGuard $ \resultType functionOutput firstActual firstFormal secondActual secondFormal ->
                        withActualsFor
                            [(firstActual, firstFormal), (secondActual, secondFormal)]
                            (functionOutput `isSubtypeOf` resultType)
                term =
                    Term.Node
                        ( RefinedSymbol
                            "binary-app"
                            true
                        )
                        [ Term.Node (RefinedSymbol "result" expected) []
                        , Term.Node (RefinedSymbol "output" dependent) []
                        , Term.Node (RefinedSymbol "x" true) []
                        , Term.Node (RefinedSymbol "n" true) []
                        , Term.Node (RefinedSymbol "y" true) []
                        , Term.Node (RefinedSymbol "m" true) []
                        ]
            evaluateConstraint equalityEntailment guard term >>= (`shouldBe` Yes)

        it "keeps distinct actual values with the same constructor separate" $
            withZ3 declarations $ \solver -> do
                let guard requirement =
                        Substitute
                            [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
                            (Satisfies (path []) requirement)
                evaluateGuard solver (guard false) collidingActuals >>= (`shouldBe` No)
                evaluateGuard solver (guard $ variable "x" .< variable "y") collidingActuals
                    >>= (`shouldBe` Yes)

        it "reports unsupported fresh declarations to a simple entailment callback" $ do
            let solver = Entailment $ \_ _ -> pure Yes
                guard =
                    Substitute
                        [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
                        (Satisfies (path []) false)
            evaluateGuard solver guard collidingActuals >>= (`shouldBe` Unknown)

        it "uses one actual value when several formals refer to the same position" $
            withZ3 declarations $ \solver -> do
                let guard =
                        Substitute
                            [Substitution (path [0]) (path [2]), Substitution (path [0]) (path [3])]
                            (Satisfies (path []) $ variable "x" .== variable "y")
                evaluateGuard solver guard collidingActuals >>= (`shouldBe` Yes)

        it "preserves ambient identity for repeated occurrences of one named leaf" $
            withZ3Assuming declarations [variable "x" .== 7] $ \solver -> do
                let guard requirement =
                        Substitute
                            [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
                            (Satisfies (path []) requirement)
                    term =
                        Term.Node
                            ( RefinedSymbol
                                "pair"
                                true
                            )
                            [ Term.Node (RefinedSymbol "x" true) []
                            , Term.Node (RefinedSymbol "x" true) []
                            , Term.Node (RefinedSymbol "y" true) []
                            , Term.Node (RefinedSymbol "z" true) []
                            ]
                evaluateGuard solver (guard $ variable "y" .== 7) term >>= (`shouldBe` Yes)
                evaluateGuard solver (guard $ variable "y" .== variable "z") term >>= (`shouldBe` Yes)

        it "applies a swap simultaneously instead of rewriting its replacements" $
            withZ3 declarations $ \solver -> do
                let guard =
                        Substitute
                            [Substitution (path [0]) (path [1]), Substitution (path [1]) (path [0])]
                            (Satisfies (path []) $ variable "x" .== variable "y")
                    term = Term.Node (RefinedSymbol "pair" true) [Term.Node (RefinedSymbol "x" true) [], Term.Node (RefinedSymbol "y" true) []]
                evaluateGuard solver guard term >>= (`shouldBe` No)

        it "does not swap the value assumptions of actual arguments" $
            withZ3 declarations $ \solver -> do
                let guard =
                        Substitute
                            [Substitution (path [0]) (path [1]), Substitution (path [1]) (path [0])]
                            (Satisfies (path []) $ variable "x" .< variable "y")
                    term =
                        Term.Node
                            ( RefinedSymbol
                                "pair"
                                true
                            )
                            [ Term.Node (RefinedSymbol "x" (variable valueName .== 0)) []
                            , Term.Node (RefinedSymbol "y" (variable valueName .== 1)) []
                            ]
                evaluateGuard solver guard term >>= (`shouldBe` No)

        it "composes nested scopes from the inner scope to the outer scope" $
            withZ3 declarations $ \solver -> do
                let guard =
                        Substitute [Substitution (path [0]) (path [1])]
                            $ Substitute [Substitution (path [1]) (path [2])]
                            $ Satisfies (path [])
                            $ variable "y" .== variable "z"
                    term =
                        Term.Node
                            ( RefinedSymbol
                                "triple"
                                true
                            )
                            [Term.Node (RefinedSymbol "z" true) [], Term.Node (RefinedSymbol "x" true) [], Term.Node (RefinedSymbol "y" true) []]
                evaluateGuard solver guard term >>= (`shouldBe` Yes)

        it "keeps actual refinements in their ambient environment under nested scopes" $
            withZ3Assuming declarations [variable "z" .== 0] $ \solver -> do
                let guard requirement =
                        Substitute [Substitution (path [0]) (path [1])]
                            $ Substitute [Substitution (path [2]) (path [3])]
                            $ Satisfies (path []) requirement
                    term =
                        Term.Node
                            ( RefinedSymbol
                                "quadruple"
                                true
                            )
                            [ Term.Node (RefinedSymbol "x" (variable valueName .== variable "z")) []
                            , Term.Node (RefinedSymbol "y" true) []
                            , Term.Node (RefinedSymbol "w" (variable valueName .== 1)) []
                            , Term.Node (RefinedSymbol "z" true) []
                            ]
                evaluateGuard solver (guard $ variable "y" .== variable "w") term >>= (`shouldBe` No)
                evaluateGuard solver (guard $ variable "y" .< variable "w") term >>= (`shouldBe` Yes)

        it "renames quantified binders instead of capturing the actual variable" $
            withZ3 declarations $ \solver -> do
                let requirement =
                        Forall [("x", IntSort)] $
                            variable "y" .== variable "x"
                    guard =
                        Substitute [Substitution (path [0]) (path [1])] $
                            Satisfies (path []) requirement
                    term = Term.Node (RefinedSymbol "pair" true) [Term.Node (RefinedSymbol "x" true) [], Term.Node (RefinedSymbol "y" true) []]
                evaluateGuard solver guard term >>= (`shouldBe` No)

-- | Integer names for actual variables and constructor result values in these checks.
declarations :: [(Name, Sort)]
declarations = [(name, IntSort) | name <- [fromString valueName, "app", "w", "x", "y", "z"]]

-- | Two different applications whose result refinements identify their values.
collidingActuals :: Term Symbol
collidingActuals =
    Term.Node
        ( RefinedSymbol
            "pair"
            true
        )
        [ Term.Node (RefinedSymbol "app" (variable valueName .== 0)) [Term.Node (RefinedSymbol "zero" true) []]
        , Term.Node (RefinedSymbol "app" (variable valueName .== 1)) [Term.Node (RefinedSymbol "one" true) []]
        , Term.Node (RefinedSymbol "x" true) []
        , Term.Node (RefinedSymbol "y" true) []
        ]
