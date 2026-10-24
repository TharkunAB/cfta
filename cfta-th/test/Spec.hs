{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- The declarations that only deriveNode reads are not used otherwise.
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

-- | Generated node views: the same terms and ranks as hand-written views, and the rejected declarations.
module Main (main) where

import Data.Proxy (Proxy (Proxy))
import GHC.Generics (Generic)
import Language.Haskell.TH (recover)
import Test.Hspec (Spec, describe, hspec, it, shouldBe)

import qualified Data.CFTA.Gen as Gen
import qualified Data.CFTA.Gen.Refinement as LTA
import Data.CFTA.Gen.Refinement.Derive
import Data.CFTA.Gen.Typing
import Data.CFTA.Generic (HasFTA)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.TH (deriveNode)

-- | The source datatype of the typed language.
data Expr = Lit Int | Add Expr Expr
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | The hand-written view of 'Expr'.
data ExprManual e = LitManual e | AddManual e e
    deriving stock (Generic)
    deriving anyclass (NodeView)

-- | The source datatype of the refined language.
data Amount = Amount Integer
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | The hand-written view of 'Amount'.
newtype AmountManual e = AmountManual e
    deriving stock (Generic)
    deriving anyclass (NodeView)

-- | A record with a type parameter.
data Record a = Record {first :: a, rest :: Maybe a}

-- | A newtype.
newtype Wrap a = Wrap {unwrap :: a}

-- | A named infix constructor.
data Pair a = a `Together` a

-- | A datatype with no constructors.
data Empty

-- | A GADT.
data Gadt a where
    Gadt :: Int -> Gadt Int

-- | An existential constructor.
data Existential = forall a. (Show a) => Existential a

-- | A symbolic name.
data a :+: b = a :+: b

-- | A type synonym.
type Synonym = Int

-- | A datatype whose view name is in scope already.
data Clash = Clash

-- | The name that the view of 'Clash' would have.
data ClashNode = ClashNode

$(deriveNode ''Expr)
$(deriveNode ''Amount)
$(deriveNode ''Record)
$(deriveNode ''Wrap)
$(deriveNode ''Pair)
$(deriveNode ''Empty)

main :: IO ()
main = hspec spec

spec :: Spec
spec = describe "deriveNode" $ do
    it "gives the same typed terms and ranks as a hand-written view" $ do
        let generated = typed $ [rule (LitNode (value n)) () | n <- [0, 1 :: Int]] <> [rule (AddNode (subterm [] ()) (subterm [] ())) ()]
            manual = typed $ [rule (LitManual (value n)) () | n <- [0, 1 :: Int]] <> [rule (AddManual (subterm [] ()) (subterm [] ())) ()]
        Gen.cardinality generated `shouldBe` Gen.cardinality manual
        Gen.values generated `shouldBe` Gen.values manual
        let terms = either (error . show) id $ Gen.values generated
        length terms `shouldBe` 38
        mapM_ (\term -> Gen.rankOfValue generated term `shouldBe` Gen.rankOfValue manual term) terms
        mapM_ (\term -> (Gen.unrank generated =<< Gen.rankOfValue generated term) `shouldBe` Right term) terms

    it "gives the same refined terms and ranks as a hand-written view" $ do
        generated <- refined $ Measured (\(AmountNode x) -> x) (\(AmountNode x) -> 0 .<= x .&& x .<= 2)
        manual <- refined $ Measured (\(AmountManual x) -> x) (\(AmountManual x) -> 0 .<= x .&& x .<= 2)
        LTA.values generated `shouldBe` LTA.values manual
        map (LTA.unrank generated) [0 .. 3] `shouldBe` map (LTA.unrank manual) [0 .. 3]

    it "keeps the constructors in order with their field counts" $ do
        fieldCounts (Proxy @RecordNode) `shouldBe` Just [("RecordNode", 2)]
        fieldCounts (Proxy @WrapNode) `shouldBe` Just [("WrapNode", 1)]
        fieldCounts (Proxy @PairNode) `shouldBe` Just [("TogetherNode", 2)]
        fieldCounts (Proxy @ExprNode) `shouldBe` Just [("LitNode", 1), ("AddNode", 2)]
        nodeShape (Proxy @EmptyNode) `shouldBe` Just []
        nodeFields (RecordNode (3 :: Int) 4) `shouldBe` (0, [Just 3, Just 4])

    it "rejects the declarations that need a hand-written view" $
        [ $(recover [|True|] (deriveNode ''Gadt >> [|False|]))
        , $(recover [|True|] (deriveNode ''Existential >> [|False|]))
        , $(recover [|True|] (deriveNode ''(:+:) >> [|False|]))
        , $(recover [|True|] (deriveNode ''Synonym >> [|False|]))
        , $(recover [|True|] (deriveNode ''Clash >> [|False|]))
        ]
            `shouldBe` replicate 5 True
  where
    typed rules = either (error . show) id (fromTypingRules (Typing (Nesting 2) [] [()] rules)) :: Gen.Gen Symbol Expr
    refined measured = LTA.compile $ either (error . show) id $ deriveLTAFrom @Amount 0 (atom @Integer LTA.every) measured
    fieldCounts proxy = map (fmap length) <$> nodeShape proxy
