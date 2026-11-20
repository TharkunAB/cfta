{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.SyntaxSpec (spec) where

import qualified Data.Set as Set

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldMatchList, shouldSatisfy)

import qualified Data.CFTA as FTA
import Data.CFTA.Refinement (
    AutomatonError (CyclicGuardReference, GuardArityMismatch, OpenAutomaton),
    Guard (Entails, Satisfies),
    Node (Mu, Node, Rec),
    RecNodeId (RecUnint),
    StratificationError (NonDecreasingIndex),
    Symbol (RefinedSymbol),
    Verdict (..),
    accepts,
    automatonAlphabet,
    constraintAsGuard,
    denotationAtMost,
    edgeChildren,
    edgeConstraint,
    edgeSymbol,
    fromStratified,
    mkEdge,
    noConstraint,
    nodeEdges,
    path,
    semanticConstraint,
    validate,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (refinementFormula, true, (.==), (.>=))
import Data.CFTA.Refinement.Guard (automaton, contract, isSubtypeOf, requires, transition)
import Data.CFTA.Refinement.TestSupport (tableEntailment)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec =
    describe "named guards and validation" $ do
        it "reports a named guard with the wrong number of arguments" $ do
            let leaf = Node [Transition "leaf" true [] noConstraint]
            automaton [transition "wrap" (const true) [leaf] (\actual expected -> actual `isSubtypeOf` expected)]
                `shouldBe` Left (GuardArityMismatch "wrap" 1 2)

        it "reports a contract that names more terms than the constructor has children" $ do
            let leaf = Node [Transition "leaf" true [] noConstraint]
            automaton [transition "pair" (const true) [leaf, leaf] (contract (\x y z -> x + y .== z))]
                `shouldBe` Left (GuardArityMismatch "pair" 2 3)
            either (const False) (const True) (automaton [transition "pair" (const true) [leaf, leaf] (contract (\x y -> x .== y))])
                `shouldBe` True

        it "builds transitions from refinements and named guards" $ do
            let nonNegative v = v .>= 0
                built = do
                    zero <- automaton [transition "zero" nonNegative [] noConstraint]
                    automaton [transition "sqrt" (const true) [zero] (`requires` nonNegative)]
            case built of
                Left err -> expectationFailure $ show err
                Right root ->
                    accepts
                        tableEntailment
                        root
                        (Term.Node (RefinedSymbol "sqrt" true) [Term.Node (RefinedSymbol "zero" (refinementFormula nonNegative)) []])
                        >>= (`shouldBe` Yes)

        it "interprets entailments carried by interned edges" $ do
            let nonNegative = refinementFormula (\v -> v .>= 0)
                alternatives =
                    Node
                        [ Transition "zero" nonNegative [] noConstraint
                        , Transition "unknown" true [] noConstraint
                        ]
                root =
                    Node
                        [ mkEdge
                            (RefinedSymbol "check" true)
                            [alternatives, alternatives]
                            (semanticConstraint $ Entails (path [0]) (path [1]))
                        ]
                terms =
                    [ Term.Node (RefinedSymbol "check" true) [left, right]
                    | left <- [Term.Node (RefinedSymbol "zero" nonNegative) [], Term.Node (RefinedSymbol "unknown" true) []]
                    , right <- [Term.Node (RefinedSymbol "zero" nonNegative) [], Term.Node (RefinedSymbol "unknown" true) []]
                    ]
            validate root `shouldBe` Right ()
            automatonAlphabet root `shouldSatisfy` Set.member (RefinedSymbol "zero" nonNegative)
            map (constraintAsGuard . edgeConstraint) (nodeEdges root)
                `shouldBe` [Entails (path [0]) (path [1])]
            mapM (accepts tableEntailment root) terms
                >>= (`shouldBe` [Yes, Yes, No, Yes])
            denotationAtMost tableEntailment 1 root
                >>= either (expectationFailure . show) (`shouldMatchList` map (terms !!) [0, 1, 3])

        it "rejects a guard position inside a recursive node" $ do
            let root = Mu $ \self ->
                    Node
                        [ mkEdge
                            (RefinedSymbol "loop" true)
                            [self]
                            (semanticConstraint $ Satisfies (path [0]) true)
                        ]
            case validate root of
                Left (CyclicGuardReference _ target) -> target `shouldBe` path [0]
                other -> expectationFailure $ show other

        it "rejects free recursive references" $
            validate (Rec $ RecUnint 0) `shouldBe` Left OpenAutomaton

        it "rejects reachable dependencies that stay level or increase" $ do
            let step child = FTA.Transition "step" [child] noConstraint
                same _ = [step 1]
                equalRank _ = [step False]
                increases 2 = [step 1]
                increases _ = [step 2]
            fromStratified id same 1 `shouldBe` Left (NonDecreasingIndex 1 1)
            fromStratified (const 0) equalRank True `shouldBe` Left (NonDecreasingIndex True False)
            fromStratified id increases 2 `shouldBe` Left (NonDecreasingIndex 1 2)

        it "shares a decreasing child and keeps the transition's refinements and guard" $ do
            let nonNegative v = v .>= 0
                guard = path [0] `requires` nonNegative
                pair = RefinedSymbol "pair" (refinementFormula (.== 1))
                leaf = RefinedSymbol "zero" (refinementFormula nonNegative)
                rows 1 = [FTA.Transition pair [0, 0] guard]
                rows _ = [FTA.Transition leaf [] noConstraint]
            case fromStratified id rows 1 of
                Left err -> expectationFailure $ show err
                Right root -> case nodeEdges root of
                    [edge] -> do
                        edgeSymbol edge `shouldBe` pair
                        edgeConstraint edge `shouldBe` guard
                        case edgeChildren edge of
                            [left, right] -> do
                                left `shouldBe` right
                                map edgeSymbol (nodeEdges left) `shouldBe` [leaf]
                            other -> expectationFailure $ show other
                        let zero = Term.Node leaf []
                        accepts tableEntailment root (Term.Node pair [zero, zero]) >>= (`shouldBe` Yes)
                    other -> expectationFailure $ show other
