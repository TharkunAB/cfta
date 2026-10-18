{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- The declarations that only deriveNode reads are not used otherwise.
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

-- | Generated node views against hand-written views, quoted graphs against built graphs, and the rejected input.
module Main (main) where

import Data.Proxy (Proxy (Proxy))
import qualified Data.Text as Text
import GHC.Generics (Generic)
import Language.Haskell.TH (recover)
import Language.Haskell.TH.Quote (quoteExp)
import Test.Hspec (Spec, describe, hspec, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalityConstraint, noConstraint)
import qualified Data.CFTA.Document as D
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Path (path)
import qualified Data.CFTA.Refinement.Expression as Expression
import Data.CFTA.Serialization.Text (StateCodec (StateCodec), TextError (InvalidDefinition), parseGraphWith)

import qualified Data.CFTA.Gen as Gen
import qualified Data.CFTA.Gen.Refinement as LTA
import Data.CFTA.Gen.Refinement.Derive
import Data.CFTA.Gen.Typing
import Data.CFTA.Generic (HasFTA)
import Data.CFTA.Symbol (Symbol (RefinedSymbol))
import Data.CFTA.TH (automaton, deriveNode)

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

-- | An atom with the value 0.
zero :: Symbol
zero = RefinedSymbol "zero" $ Expression.refinementFormula (Expression..== 0)

-- | An atom with the value 1.
one :: Symbol
one = RefinedSymbol "one" $ Expression.refinementFormula (Expression..== 1)

-- | The two children are equal.
equalChildren :: Constraint
equalChildren = equalityConstraint $ mkEqConstraints [[path [0], path [1]]]

$(deriveNode ''Expr)
$(deriveNode ''Amount)
$(deriveNode ''Record)
$(deriveNode ''Wrap)
$(deriveNode ''Pair)
$(deriveNode ''Empty)

main :: IO ()
main = hspec $ do
    nodeViews
    quotes

nodeViews :: Spec
nodeViews = describe "deriveNode" $ do
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

quotes :: Spec
quotes = describe "automaton" $ do
    it "reads the graph format without its first line" $
        [automaton| start N; state N { zero @{ v == 0 }; succ(N); } |]
            `shouldBe` parseGraphWith (StateCodec Text.pack (Right . Text.unpack)) "graph 1; start N; state N { zero @{ v == 0 }; succ(N); }"

    it "puts Haskell values in place of their names" $
        [automaton|
            start Pair;
            state Pair { pair(Atom, Atom) where $equalChildren; }
            state Atom { $zero; $Main.one; }
        |]
            `shouldBe` Right
                ( either (error . show) id $
                    FTA.mkFTA
                        "Pair"
                        [ ("Pair", [FTA.Transition "pair" ["Atom", "Atom"] equalChildren])
                        , ("Atom", [FTA.Transition zero [] noConstraint, FTA.Transition one [] noConstraint])
                        ]
                )

    it "checks the symbol arities when the expression is evaluated" $
        [automaton| start S; state S { $zero; $Main.zero(S); } |] `shouldSatisfy` \case
            Left (InvalidDefinition (D.InvalidGraph FTA.InconsistentArity{})) -> True
            _ -> False

    it "rejects a bad quote at compile time" $
        [ $(recover [|True|] (quoteExp automaton "start S; state S { a( ; }" >> [|False|]))
        , $(recover [|True|] (quoteExp automaton "start S; state S { $missing; }" >> [|False|]))
        , $(recover [|True|] (quoteExp automaton "start S; state S { a(T); }" >> [|False|]))
        , $(recover [|True|] (quoteExp automaton "start T; state S {}" >> [|False|]))
        , $(recover [|True|] (quoteExp automaton "start S; state S {} state S {}" >> [|False|]))
        ]
            `shouldBe` replicate 5 True
