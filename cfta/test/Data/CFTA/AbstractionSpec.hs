{-# LANGUAGE OverloadedStrings #-}

-- | Checks of an abstraction extension: cover, soundness, and overlaps of refined variants.
module Data.CFTA.AbstractionSpec (spec) where

import Control.Exception (throwIO)
import qualified Data.Map.Strict as Map
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.CFTA as FTA
import Data.CFTA.Abstraction (AbstractionError (..), Overlap (..))
import qualified Data.CFTA.Abstraction as Abstraction
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Formula (Formula (Top), disjunction)
import Data.CFTA.Refinement.Expression (Expr, modulo, refinementFormula, (.&&), (.<=), (.==), (.>), (.>=))
import Data.CFTA.Refinement.LiquidFixpoint (TimeLimitReached (..), withZ3)
import Data.CFTA.Refinement.Verdict (Entailment (Entailment), Verdict (..))
import Data.CFTA.Symbol (Symbol (RefinedSymbol), symbolRefinement)

spec :: Spec
spec = describe "abstraction extensions" $ do
    it "accept digits split by a new predicate" $ withZ3 [] $ \z3 -> do
        let later = sums [above4, upTo4]
        Abstraction.checkAbstraction z3 earlier later >>= (`shouldBe` [])
        Abstraction.checkOverlaps z3 later >>= (`shouldBe` [])

    it "accept digits split by parity" $ withZ3 [] $ \z3 -> do
        let later = sums [even', odd']
        Abstraction.checkAbstraction z3 earlier later >>= (`shouldBe` [])
        Abstraction.checkOverlaps z3 later >>= (`shouldBe` [])

    it "report a digit that no variant has" $ withZ3 [] $ \z3 -> do
        -- Five is in no variant.
        let above5 = digit $ \v -> range v .&& v .> 5
        Abstraction.checkAbstraction z3 earlier (sums [above5, upTo4])
            >>= (`shouldBe` [Uncovered "e" (digit range) [above5, upTo4] No])

    it "report a variant with a new value" $ withZ3 [] $ \z3 -> do
        let unbounded = digit (.> 4)
        Abstraction.checkAbstraction z3 earlier (sums [unbounded, upTo4])
            >>= (`shouldBe` [Unsound "e" unbounded [digit range] No])

    it "report an added refinement that loses values" $ withZ3 [] $ \z3 ->
        Abstraction.checkAbstraction z3 earlier (sums [even'])
            >>= (`shouldBe` [Uncovered "e" (digit range) [even'] No])

    it "report a new production as a variant without productions" $ withZ3 [] $ \z3 -> do
        let negation = node "neg" ["e"]
        Abstraction.checkAbstraction z3 earlier (sums [digit range, negation])
            >>= (`shouldBe` [Unsound "e" negation [] No])

    it "report another initial state" $ withZ3 [] $ \z3 -> do
        let rows = [("e", [digit range, add]), ("f", [digit range, node "add" ["f", "f"]])]
        Abstraction.checkAbstraction z3 (automaton "e" rows) (automaton "f" rows) >>= (`shouldBe` [ChangedStart "e" "f"])

    it "warn about two variants with a common value" $ withZ3 [] $ \z3 -> do
        -- Four is in both variants.
        let from4 = digit $ \v -> range v .&& v .>= 4
            later = sums [from4, upTo4]
        Abstraction.checkAbstraction z3 earlier later >>= (`shouldBe` [])
        Abstraction.checkOverlaps z3 later >>= (`shouldBe` [Overlap "e" from4 upTo4 No])

    it "keep an unknown verdict unknown" $ do
        -- The table decides each question of the split except the cover and the overlap.
        let table =
                Map.fromList
                    [ ((Top, Top), Yes)
                    , ((formula above4, disjunction [formula $ digit range]), Yes)
                    , ((formula upTo4, disjunction [formula $ digit range]), Yes)
                    ]
            solver = Entailment $ \antecedent consequent -> pure $ Map.findWithDefault Unknown (antecedent, consequent) table
            later = sums [above4, upTo4]
        Abstraction.checkAbstraction solver earlier later >>= (`shouldBe` [Uncovered "e" (digit range) [above4, upTo4] Unknown])
        Abstraction.checkOverlaps solver later >>= (`shouldBe` [Overlap "e" above4 upTo4 Unknown])

    it "read a time limit as unknown" $ do
        let solver = Entailment $ \_ _ -> throwIO $ TimeLimitReached 1
            later = sums [above4, upTo4]
        Abstraction.checkAbstraction solver earlier later
            >>= ( `shouldBe`
                    [ Uncovered "e" (digit range) [above4, upTo4] Unknown
                    , Uncovered "e" add [add] Unknown
                    , Unsound "e" above4 [digit range] Unknown
                    , Unsound "e" upTo4 [digit range] Unknown
                    , Unsound "e" add [add] Unknown
                    ]
                )
  where
    above4 = digit $ \v -> range v .&& v .> 4
    upTo4 = digit $ \v -> range v .&& v .<= 4
    even' = digit $ \v -> range v .&& modulo v 2 .== 0
    odd' = digit $ \v -> range v .&& modulo v 2 .== 1
    add = node "add" ["e", "e"]
    formula = symbolRefinement . FTA.transitionSymbol

-- | The digits, as values from zero to nine.
range :: Expr -> Formula
range v = v .>= 0 .&& v .<= 9

-- | Sums of the digits.
earlier :: FTA.PlainFTA String Symbol
earlier = sums [digit range]

-- | Sums of the given leaves at state @e@.
sums :: [FTA.Transition String Symbol Constraint] -> FTA.PlainFTA String Symbol
sums leaves = automaton "e" [("e", leaves <> [node "add" ["e", "e"]])]

-- | A leaf @lit@ with the refinement.
digit :: (Expr -> Formula) -> FTA.Transition String Symbol Constraint
digit refinement = FTA.Transition (RefinedSymbol "lit" $ refinementFormula refinement) [] noConstraint

-- | A production without a constraint.
node :: Symbol -> [String] -> FTA.Transition String Symbol Constraint
node symbol children = FTA.Transition symbol children noConstraint

-- | An automaton from rows of named states.
automaton :: String -> [(String, [FTA.Transition String Symbol Constraint])] -> FTA.PlainFTA String Symbol
automaton initial rows = either (error . show) id $ FTA.mkFTA initial rows
