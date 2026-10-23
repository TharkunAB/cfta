{-# LANGUAGE OverloadedStrings #-}

-- | Checks of a definitional extension, with counterexample terms.
module Data.CFTA.ExtensionSpec (spec) where

import Control.Monad (forM_)
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalityConstraint, noConstraint)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Extension (ExtensionError (..))
import qualified Data.CFTA.Extension as Extension
import Data.CFTA.Lowering (Expansion (..), LoweringError (..))
import qualified Data.CFTA.Lowering as Lowering
import Data.CFTA.Path (path)
import qualified Data.CFTA.Sized as Sized
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term (Node))

spec :: Spec
spec = describe "Data.CFTA.Extension" $ do
    it "accepts a definitional extension" $
        Extension.checkExtension lowering earlier later `shouldBe` Right []

    it "keeps every old term and its meaning when it accepts an extension" $ do
        -- The terms of the earlier automaton up to size seven.
        let classes = either (error . show) id $ Sized.sized earlier
            old = concatMap (Sized.termsOfSize classes) [1 .. 7]
        length old `shouldSatisfy` (> 50)
        forM_ old $ \term -> do
            FTA.accepts later term `shouldBe` True
            Lowering.lower lowering term `shouldBe` Just term

    it "reports a lost production with an old term that uses it" $ do
        let withoutOne = automaton "e" [("e", [leaf "zero", node "add" ["e", "e"], node "double" ["e"]])]
        Extension.checkExtension lowering earlier withoutOne `shouldBe` Right [LostProduction "e" (leaf "one") (Just one)]

    it "reports a changed production as lost, and its new form as not lowered" $ do
        let old = automaton "e" [("e", [leaf "zero", node "add" ["e", "n"]]), ("n", [leaf "one"])]
            new = automaton "e" [("e", [leaf "zero", node "add" ["n", "e"]]), ("n", [leaf "one"])]
        Extension.checkExtension Lowering.identity old new
            `shouldBe` Right
                [ LostProduction "e" (node "add" ["e", "n"]) (Just $ add zero one)
                , RejectedLowering "e" (node "add" ["n", "e"]) (add one zero) (add one zero)
                ]

    it "reports another initial state" $ do
        let rows = [("e", [leaf "zero", node "add" ["e", "n"]]), ("n", [leaf "one"])]
        Extension.checkExtension Lowering.identity (automaton "e" rows) (automaton "n" rows)
            `shouldBe` Right [ChangedStart "e" "n"]

    it "reports an old constructor that the lowering expands" $ do
        let swapped = mkLowering [("double", 1, Apply "add" [Child 0, Child 0]), ("add", 2, Apply "add" [Child 1, Child 0])]
        Extension.checkExtension swapped earlier (digits [("double", 1)]) `shouldBe` Right [LoweredOldConstructor "add"]
        -- An old term changes its meaning.
        Lowering.lower swapped (add zero one) `shouldBe` Just (add one zero)

    it "reports a production that does not lower, with a term that uses it and its lowering" $ do
        let wrong = mkLowering [("double", 1, Apply "mul" [Child 0, Child 0])]
            new = digits [("double", 1)]
            term = Node "double" [one]
        Extension.checkExtension wrong earlier new
            `shouldBe` Right [RejectedLowering "e" (node "double" ["e"]) term (Node "mul" [one, one])]
        FTA.accepts new term `shouldBe` True
        FTA.accepts earlier (Node "mul" [one, one]) `shouldBe` False

    it "reports a production with another number of children than its expansion, with a term that does not lower" $ do
        let new = digits [("double", 2)]
            term = Node "double" [one, one]
        Extension.checkExtension lowering earlier new `shouldBe` Right [NotTotal "e" (node "double" ["e", "e"]) (Just term)]
        FTA.accepts new term `shouldBe` True
        Lowering.lower lowering term `shouldBe` Nothing

    it "gives no counterexample when the smallest term through a production lowers into the earlier automaton" $ do
        -- The states a and b accept the same terms, so the check of the states
        -- does not show that double(b) lowers, but add(one, one) is a term of s.
        let old = automaton "s" [("s", [node "add" ["a", "a"]]), ("a", [leaf "one"]), ("b", [leaf "one"])]
            new = automaton "s" [("s", [node "add" ["a", "a"], node "double" ["b"]]), ("a", [leaf "one"]), ("b", [leaf "one"])]
            term = Node "double" [one]
        Extension.checkExtension lowering old new
            `shouldBe` Right [UnprovedLowering "s" (node "double" ["b"]) (Just (term, add one one))]
        FTA.accepts new term `shouldBe` True

    it "reports a production that no term uses without a term" $ do
        let new = automaton "e" [("e", zeroOneAdd <> [node "double" ["e"]]), ("u", [node "double" ["u"]])]
        Extension.checkExtension lowering earlier new
            `shouldBe` Right [UnprovedLowering "u" (node "double" ["u"]) Nothing]

    it "rejects a transition with a constraint" $ do
        let equalChildren = equalityConstraint $ mkEqConstraints [[path [0], path [1]]]
            new = automaton "e" [("e", [leaf "zero", leaf "one", FTA.Transition "add" ["e", "e"] equalChildren])]
        Extension.checkExtension lowering earlier new `shouldBe` Left (ConstrainedTransition "e" "add")
  where
    zero = Node "zero" []
    one = Node "one" []
    add left right = Node "add" [left, right]

-- | @double(x) -> add(x, x)@ and @succ(x) -> add(x, one)@.
lowering :: Lowering.Lowering Symbol
lowering = mkLowering [("double", 1, Apply "add" [Child 0, Child 0]), ("succ", 1, Apply "add" [Child 0, Apply "one" []])]

-- | A lowering that must be valid.
mkLowering :: [(Symbol, Int, Expansion Symbol)] -> Lowering.Lowering Symbol
mkLowering = either (error . show) id . Lowering.mkLowering

-- | Sums of zero and one.
earlier :: FTA.PlainFTA String Symbol
earlier = digits []

-- | Sums of zero and one, with double and succ.
later :: FTA.PlainFTA String Symbol
later = digits [("double", 1), ("succ", 1)]

-- | One state @e@ with zero, one, add, and the given constructors over that state.
digits :: [(Symbol, Int)] -> FTA.PlainFTA String Symbol
digits extra = automaton "e" [("e", zeroOneAdd <> [node symbol (replicate arity "e") | (symbol, arity) <- extra])]

-- | The productions of the sums of zero and one at state @e@.
zeroOneAdd :: [FTA.Transition String Symbol Constraint]
zeroOneAdd = [leaf "zero", leaf "one", node "add" ["e", "e"]]

-- | An automaton from rows of named states.
automaton :: String -> [(String, [FTA.Transition String Symbol Constraint])] -> FTA.PlainFTA String Symbol
automaton initial rows = either (error . show) id $ FTA.mkFTA initial rows

-- | A production without children.
leaf :: Symbol -> FTA.Transition String Symbol Constraint
leaf symbol = node symbol []

-- | A production without a constraint.
node :: Symbol -> [String] -> FTA.Transition String Symbol Constraint
node symbol children = FTA.Transition symbol children noConstraint
