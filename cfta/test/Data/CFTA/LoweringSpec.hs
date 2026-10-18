{-# LANGUAGE OverloadedStrings #-}

-- | Template lowerings: lowered terms, the inverse image of a spec, and the check of a later grammar.
module Data.CFTA.LoweringSpec (spec) where

import Control.Monad ((>=>))
import qualified Data.Set as Set
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (noConstraint)
import Data.CFTA.Lowering (Expansion (..), ExpansionError (..), LoweringError (..))
import qualified Data.CFTA.Lowering as Lowering
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term (Node))

-- | The states of the specs: the parity of the value of a term.
data Parity = Even | Odd
    deriving (Eq, Ord, Show)

spec :: Spec
spec = describe "template lowerings" $ do
    it "put the lowered children in the expansion" $ do
        Lowering.lower lowering (double one) `shouldBe` Just (add one one)
        Lowering.lower lowering (successor (double zero)) `shouldBe` Just (add (add zero zero) one)
        Lowering.lower lowering (add one zero) `shouldBe` Just (add one zero)

    it "lift a spec to the terms whose lowering it accepts" $ do
        lifted <- either (fail . show) pure $ Lowering.lift lowering evenValue
        let within = either (error . show) FTA.dropConstraints $ FTA.intersect later lifted
            bounded = Set.fromList $ FTA.terms $ FTA.boundDepth 3 later
            expected = Set.filter (maybe False (FTA.accepts evenValue) . Lowering.lower lowering) bounded
        Set.fromList (FTA.terms $ FTA.boundDepth 3 within) `shouldBe` expected
        Set.size expected `shouldSatisfy` (> 10)

    it "compose: lowering with a composite is lowering twice" $ do
        -- quad(x) lowers to double(double(x)), which lowers to sums.
        let upper = either (error . show) id $ Lowering.mkLowering [("quad", 1, Apply "double" [Apply "double" [Child 0]])]
            composite = Lowering.compose upper lowering
            terms = FTA.terms $ FTA.boundDepth 3 $ grammar [("double", 1), ("succ", 1), ("quad", 1)]
        length terms `shouldSatisfy` (> 10)
        map (Lowering.lower composite) terms
            `shouldBe` map (Lowering.lower upper >=> Lowering.lower lowering) terms
        map (Lowering.lower (Lowering.compose Lowering.identity lowering)) terms `shouldBe` map (Lowering.lower lowering) terms
        map (Lowering.lower (Lowering.compose lowering Lowering.identity)) terms `shouldBe` map (Lowering.lower lowering) terms
        let top = grammar [("double", 1), ("succ", 1), ("quad", 1)]
            within lifted = Set.fromList $ FTA.terms $ FTA.boundDepth 3 $ either (error . show) FTA.dropConstraints $ FTA.intersect top lifted
            once = either (error . show) id $ Lowering.lift composite evenValue
            twice = either (error . show) id $ Lowering.lift lowering evenValue >>= Lowering.lift upper
        within once `shouldBe` within twice

    it "accept a later grammar whose productions lower into the earlier grammar" $
        Lowering.checkLowering lowering earlier later `shouldBe` []

    it "report a production that does not lower" $ do
        let wrong = either (error . show) id $ Lowering.mkLowering [("double", 1, Apply "mul" [Child 0, Child 0])]
        Lowering.checkLowering wrong earlier (grammar [("double", 1)]) `shouldBe` [NotLowered () "double" [()]]

    it "reject an expansion with a child out of range" $
        Lowering.mkLowering [("double", 1, Apply "add" [Child 0, Child 1 :: Expansion Symbol])]
            `shouldBe` Left (ChildOutOfRange "double" 1)
  where
    zero = Node "zero" []
    one = Node "one" []
    add left right = Node "add" [left, right]
    double term = Node "double" [term]
    successor term = Node "succ" [term]

-- | @double(x) -> add(x, x)@ copies its child; @succ(x) -> add(x, one)@ does not.
lowering :: Lowering.Lowering Symbol
lowering =
    either (error . show) id $
        Lowering.mkLowering
            [ ("double", 1, Apply "add" [Child 0, Child 0])
            , ("succ", 1, Apply "add" [Child 0, Apply "one" []])
            ]

-- | Sums of zero and one.
earlier :: FTA.PlainFTA () Symbol
earlier = grammar []

-- | Sums of zero and one, with double and succ.
later :: FTA.PlainFTA () Symbol
later = grammar [("double", 1), ("succ", 1)]

-- | One state with zero, one, add, and the given constructors over that state.
grammar :: [(Symbol, Int)] -> FTA.PlainFTA () Symbol
grammar extra =
    either (error . show) id $
        FTA.mkFTA
            ()
            [ ((),) $
                [ FTA.Transition "zero" [] noConstraint
                , FTA.Transition "one" [] noConstraint
                , FTA.Transition "add" [(), ()] noConstraint
                ]
                    <> [FTA.Transition symbol (replicate arity ()) noConstraint | (symbol, arity) <- extra]
            ]

-- | The sums of zero and one whose value is even.
evenValue :: FTA.PlainFTA Parity Symbol
evenValue =
    either (error . show) id $
        FTA.mkFTA
            Even
            [ (Even, [leaf "zero", sum' Even Even, sum' Odd Odd])
            , (Odd, [leaf "one", sum' Even Odd, sum' Odd Even])
            ]
  where
    leaf symbol = FTA.Transition symbol [] noConstraint
    sum' left right = FTA.Transition "add" [left, right] noConstraint
