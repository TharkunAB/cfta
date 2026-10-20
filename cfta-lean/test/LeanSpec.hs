{-# LANGUAGE OverloadedStrings #-}

-- | Check the solver boundary and, when configured, the live Kimina service.
module Main (main) where

import Control.Exception (throwIO)
import Data.Either (isLeft)
import Data.IORef (modifyIORef', newIORef, readIORef)
import System.Environment (lookupEnv)
import Test.Hspec

import Data.CFTA.Formula
import Data.CFTA.Lean
import qualified Data.CFTA.Refinement as Refinement
import Data.CFTA.Refinement.Expression (refinementFormula, true, (.==))
import Data.CFTA.Refinement.LiquidFixpoint (TimeLimitReached (..), withZ3)
import Data.CFTA.Refinement.Verdict

main :: IO ()
main = do
    endpoint <- lookupEnv "CFTA_KIMINA_URL"
    let live test = case endpoint of
            Nothing -> pendingWith "set CFTA_KIMINA_URL to run the Kimina integration checks"
            Just url -> withKimina defaultOptions{optionUrl = url} [] [] test
    hspec $ do
        describe "fallback" $ do
            it "does not call the fallback after a decision" $ do
                calls <- newIORef (0 :: Int)
                let second = Entailment $ \_ _ -> modifyIORef' calls (+ 1) >> pure Unknown
                mapM_
                    (\answer -> entails (fallback (Entailment $ \_ _ -> pure answer) second) Top Bottom `shouldReturn` answer)
                    [Yes, No]
                readIORef calls `shouldReturn` 0
            it "preserves the bindings after Unknown" $ do
                let bindings = [("fresh", "original")]
                    second = entailmentWithBindings $ \actual _ _ ->
                        (actual `shouldBe` bindings) >> pure No
                    first = entailmentWithBindings $ \_ _ _ -> pure Unknown
                entailsWithBindings (fallback first second) bindings Top Bottom `shouldReturn` No
            it "uses the fallback after a Z3 time limit" $ do
                let first = Entailment $ \_ _ -> throwIO (TimeLimitReached 1)
                    second = Entailment $ \_ _ -> pure Yes
                entails (fallback first second) Top Top `shouldReturn` Yes
        describe "formula boundary" $ do
            it "rejects a fresh binding that shadows an ambient value" $
                entailmentProposition [] [Atom Eq (Var "fresh") (Lit 0)] [("fresh", "x")] Top Top
                    `shouldSatisfy` isLeft
            it "rejects division by zero instead of using Lean's value at zero" $
                entailmentProposition [] [] [] Top (Atom Eq (Div (Lit 1) (Lit 0)) (Lit 0))
                    `shouldSatisfy` isLeft
            it "rejects an inconsistent function arity" $
                entailmentProposition [] [] [] Top (Atom Eq (App "f" [Lit 0]) (App "f" [Lit 0, Lit 1]))
                    `shouldSatisfy` isLeft
        describe "Kimina entailment" $ do
            it "proves an integer implication" . live $ \solver ->
                entails solver (Atom Gt (Var "x") (Lit 0)) (Atom Ge (Var "x") (Lit 0)) `shouldReturn` Yes
            it "checks a counterexample to an implication" . live $ \solver ->
                entails solver (Atom Gt (Var "x") (Lit 0)) (Atom Gt (Var "x") (Lit 1)) `shouldReturn` No
            it "proves a nonlinear integer implication" . live $ \solver ->
                entails
                    solver
                    (And [Atom Gt (Var "x") (Lit 0), Atom Gt (Var "y") (Lit 0)])
                    (Atom Ge (Mul (Var "x") (Var "y")) (Var "x"))
                    `shouldReturn` Yes
            it "keeps quantifier shadowing separate from free values" . live $ \solver ->
                entails
                    solver
                    (Atom Eq (Var "x") (Lit 1))
                    (Forall [("x", IntSort)] (Atom Eq (Var "x") (Lit 1)))
                    >>= (`shouldSatisfy` (`elem` [No, Unknown]))
            it "supports uninterpreted functions" . live $ \solver ->
                entails
                    solver
                    (Atom Eq (Var "x") (Var "y"))
                    (Atom Eq (App "f" [Var "x"]) (App "f" [Var "y"]))
                    `shouldReturn` Yes
            it "does not interpolate source names into Lean code" . live $ \solver ->
                let name = "x\naxiom forged : False\n--"
                 in entails solver (Atom Eq (Var name) (Lit 1)) (Atom Gt (Var name) (Lit 0)) `shouldReturn` Yes
            it "uses ambient assumptions" $ case endpoint of
                Nothing -> pendingWith "set CFTA_KIMINA_URL"
                Just url ->
                    withKimina defaultOptions{optionUrl = url} [] [Atom Eq (Var "x") (Lit 3)] $ \solver ->
                        entails solver Top (Atom Gt (Var "x") (Lit 0)) `shouldReturn` Yes
            it "copies a fresh value's sort without equating its value" $ case endpoint of
                Nothing -> pendingWith "set CFTA_KIMINA_URL"
                Just url ->
                    withKimina defaultOptions{optionUrl = url} [("original", BoolSort)] [] $ \solver ->
                        entailsWithBindings solver [("fresh", "original")] Top (Atom Eq (Var "fresh") (Var "original"))
                            `shouldReturn` No
            it "can follow Z3 on a quantified conditional" . live $ \solver ->
                withZ3 [] $ \z3 -> do
                    let condition = Exists [("y", IntSort)] (Atom Eq (Var "y") (Var "x"))
                        conclusion = Atom Eq (Ite condition (Lit 7) (Lit 9)) (Lit 7)
                    entails (fallback z3 solver) Top conclusion `shouldReturn` Yes
            it "filters an LTA language with semantic guards" . live $ \solver -> do
                let zero = refinementFormula (\value -> value .== 0)
                    one = refinementFormula (\value -> value .== 1)
                    atoms =
                        Refinement.Node
                            [ Refinement.Transition "zero" zero [] Refinement.noConstraint
                            , Refinement.Transition "one" one [] Refinement.noConstraint
                            ]
                    language =
                        Refinement.Node
                            [ Refinement.Transition "keep" true [atoms] $
                                Refinement.semanticConstraint (Refinement.Satisfies (Refinement.path [0]) zero)
                            ]
                actual <- Refinement.denotationAtMost solver 1 language
                fmap length actual `shouldBe` Right 1
                withZ3 [] $ \z3 ->
                    Refinement.denotationAtMost z3 1 language `shouldReturn` actual
