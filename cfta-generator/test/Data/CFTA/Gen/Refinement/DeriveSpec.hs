{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeApplications #-}

{- | Tests of "Data.CFTA.Gen.Refinement.Derive": the derived generators of
SortedLists, SafeDivision, LiquidPairs, and RedBlackTrees have the cardinality
and the ranks of the hand-written generators of the examples.
-}
module Data.CFTA.Gen.Refinement.DeriveSpec (spec) where

-- A measure names each child, as in \x _ -> x, as a contract does.
{- HLINT ignore "Use const" -}

import Control.Monad (forM_, void)
import Data.Containers.ListUtils (nubOrd)
import qualified Data.Map.Strict as Map
import GHC.Generics (Generic)
import Test.Hspec (Expectation, Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)

import Data.CFTA.Gen.Refinement.Derive
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Generic (HasFTA)
import Data.CFTA.Index (Arity (..), Cardinality (..), Rank (..))
import Data.CFTA.Refinement.Expression (Expr, Refinement)
import Data.CFTA.Refinement.Symbolic (Measures (..), Symbolic (..), true, (.&&))

-- | A list that its invariant keeps sorted.
data SortedList = Nil | Cons Integer SortedList
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | The measure is the head. The head of the empty list is above every element.
instance HasLTA SortedList where
    invariant = Measured headOf sorted

-- | The head of a sorted list.
headOf :: (Symbolic e) => SortedList -> [e] -> e
headOf Cons{} [x, _] = x
headOf _ _ = 1000001

-- | Each element is from zero to a million, and at most the head of the rest.
sorted :: (Symbolic e) => SortedList -> [e] -> Truth e
sorted Cons{} [x, restHead] = 0 .<= x .&& x .<= 1000000 .&& x .<= restHead
sorted _ _ = true

-- | The elements of a sorted list.
toList :: SortedList -> [Integer]
toList Nil = []
toList (Cons element rest) = element : toList rest

-- | The hand-written sorted lists of SortedLists.hs.
sortedLists :: LTAGen.LTAGen [Integer]
sortedLists = LTAGen.recurUpTo 8 $ \rest -> LTAGen.oneof [nil, cons rest]
  where
    nil = LTAGen.leaf [] "nil" (.== 1000001)
    cons rest =
        LTAGen.measured
            "cons"
            (\element restHead -> element .<= restHead)
            (\element _ -> element)
            $ LTAGen.do
                element <- LTAGen.every `LTAGen.satisfying` (\v -> 0 .<= v .&& v .<= 1000000)
                elements <- rest
                LTAGen.pure (element : elements)

-- | The annotations of the sorted lists of the builtin list type.
listAnnotations :: [(String, Annotation)]
listAnnotations =
    [ ("[]", measure (1000001 :: Expr))
    , (":", contract (\x restHead -> 0 .<= x .&& x .<= 1000000 .&& x .<= restHead) <> measure (\x _ -> x))
    ]

-- | A division of twelve by a denominator that is not zero.
newtype Division = Divide Integer
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | The denominator is from zero to five, and it is not zero.
instance HasLTA Division where
    invariant = Contracted nonZero
      where
        nonZero _ [d] = 0 .<= d .&& d .<= 5 .&& d ./= 0
        nonZero _ _ = true

-- | The hand-written divisions of SafeDivision.hs.
divisions :: LTAGen.LTAGen (Integer, Integer)
divisions = LTAGen.node "divide" $ LTAGen.do
    d <- LTAGen.elements [0 .. 5] `LTAGen.satisfying` (\v -> v ./= 0)
    LTAGen.pure (d, 12 `div` d)

-- | A pair whose left value is below its right value.
data Pair = Pair Integer Integer
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | The left value is below the right value.
instance HasLTA Pair where
    invariant = Contracted below
      where
        below _ [left, right] = left .< right
        below _ _ = true

-- | Values that the solver knows only by the range that contains them.
ranged :: [(Integer, Refinement)]
ranged =
    [ (1, \v -> 0 .<= v .&& v .< 2)
    , (3, \v -> 2 .<= v .&& v .< 4)
    , (5, \v -> 4 .<= v .&& v .< 6)
    ]

-- | The hand-written pairs of LiquidPairs.hs.
pairs :: LTAGen.LTAGen (Integer, Integer)
pairs = LTAGen.guarded "pair" (\left right -> left .< right) $ LTAGen.do
    left <- LTAGen.pool ranged
    right <- LTAGen.pool ranged
    LTAGen.pure (left, right)

-- | The shape of a red-black tree.
data Tree = Leaf | Black Tree Tree | Red Tree Tree
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | The black height and the color of each tree, and the rules of red-black trees.
instance HasLTA Tree where
    invariant = MeasuredBy measures balanced
      where
        bh child = childMeasure "bh" child
        col child = childMeasure "col" child
        measures Black{} [left, _] = [("bh", bh left + 1), ("col", 0)]
        measures Red{} [left, _] = [("bh", bh left), ("col", 1)]
        measures _ _ = [("bh", 0), ("col", 0)]
        balanced Black{} [left, right] = bh left .== bh right
        balanced Red{} [left, right] = bh left .== bh right .&& col left .== 0 .&& col right .== 0
        balanced _ _ = true

-- | The derived red-black trees: a black root and a black height of at most three.
derivedTrees :: Either DeriveLTAError (LTAGen.LTAGen Tree)
derivedTrees = (`LTAGen.satisfying` root) <$> deriveLTA @Tree 6 mempty
  where
    root v = childMeasure "col" v .== 0 .&& childMeasure "bh" v .<= 3

-- | The two-state generator of RedBlackTrees.hs, with the bound 3.
redBlackTrees :: LTAGen.LTAGen Tree
redBlackTrees = LTAGen.recurUpTo 3 $ \blackRooted ->
    let anyRooted = LTAGen.oneof [blackRooted, red blackRooted]
     in LTAGen.oneof [leaf, black anyRooted]
  where
    leaf = LTAGen.leaf Leaf "leaf" (.== 0)
    black child =
        LTAGen.measured
            "black"
            (\leftHeight rightHeight -> leftHeight .== rightHeight)
            (\leftHeight _ -> leftHeight + 1)
            (Black <$> child <*> child)
    red child =
        LTAGen.measured
            "red"
            (\leftHeight rightHeight -> leftHeight .== rightHeight)
            (\leftHeight _ -> leftHeight)
            (Red <$> child <*> child)

{- | Compile both generators, and expect the same cardinality and the same
value at each checked rank: every rank of a small generator, and the first
three, the middle, the last two, and 200 ranks of a fixed sequence of a large
one.
-}
sameRanks :: (Eq a, Show a) => LTAGen.LTAGen a -> Either DeriveLTAError (LTAGen.LTAGen a) -> Expectation
sameRanks handWritten derived = case derived of
    Left err -> expectationFailure $ show err
    Right generator -> do
        expected <- LTAGen.compile handWritten
        actual <- LTAGen.compile generator
        LTAGen.cardinality actual `shouldBe` LTAGen.cardinality expected
        case LTAGen.cardinality expected of
            Left err -> expectationFailure $ show err
            Right (Cardinality total) -> do
                let next rank = (rank * 6364136223846793005 + 1442695040888963407) `mod` total
                    checked
                        | total <= 100000 = [0 .. total - 1]
                        | otherwise = nubOrd $ [0, 1, 2, total `div` 2, total - 2, total - 1] <> take 200 (iterate next 1)
                forM_ checked $ \rank -> LTAGen.unrank actual (Rank rank) `shouldBe` LTAGen.unrank expected (Rank rank)

spec :: Spec
spec = describe "Data.CFTA.Gen.Refinement.Derive" $ do
    it "derives SortedLists from annotations with the ranks of the hand-written generator"
        $ sameRanks sortedLists
        $ deriveLTAWith @[Integer] 8 (atom @Integer LTAGen.every) listAnnotations
    it "derives SortedLists from a HasLTA instance with the ranks of the hand-written generator"
        $ sameRanks sortedLists
        $ fmap toList <$> deriveLTA @SortedList 8 (atom @Integer LTAGen.every)
    it "derives SafeDivision from a HasLTA instance with the ranks of the hand-written generator"
        $ sameRanks divisions
        $ fmap (\(Divide d) -> (d, 12 `div` d)) <$> deriveLTA @Division 0 (atom @Integer (LTAGen.elements [0 .. 5]))
    it "derives LiquidPairs from a HasLTA instance with the ranks of the hand-written generator"
        $ sameRanks pairs
        $ fmap (\(Pair left right) -> (left, right)) <$> deriveLTA @Pair 0 (atom @Integer (LTAGen.pool ranged))
    it "gives the formulas of the annotations from the functions of the invariant" $ do
        let formulas annotations = [(name, annotationFormulas annotation) | (name, annotation) <- annotations]
        formulas (invariantAnnotations (invariant @SortedList))
            `shouldBe` formulas (zip ["Nil", "Cons"] (map snd listAnnotations))
    it "checks values with the functions of the invariant" $ do
        let atoms = atom @Integer LTAGen.every
            rules = invariant @SortedList
        map (holds atoms rules) [Cons 1 (Cons 2 (Cons 2 Nil)), Cons 3 (Cons 1 Nil), Cons 2000000 Nil]
            `shouldBe` [True, False, False]
        map (measureOf atoms rules) [Cons 4 (Cons 5 Nil), Nil] `shouldBe` [Just 4, Just 1000001]
    it "derives RedBlackTrees with named measures with the ranks of the two-state generator" $
        sameRanks redBlackTrees derivedTrees
    it "checks red-black trees with the named measures of the invariant" $ do
        let rules = invariant @Tree
        compiled <- either (fail . show) LTAGen.compile derivedTrees
        sampled <- either (fail . show) pure $ traverse (LTAGen.unrank compiled . Rank) [0, 257281604 .. 25728160404]
        filter (not . holds mempty rules) sampled `shouldBe` []
        holds mempty rules (Black (Red (Red Leaf Leaf) (Red Leaf Leaf)) Leaf) `shouldBe` False
        holds mempty rules (Black (Black Leaf Leaf) Leaf) `shouldBe` False
        measuresOf mempty rules (Black (Red (Black Leaf Leaf) (Black Leaf Leaf)) (Black Leaf Leaf))
            `shouldBe` Map.fromList [("bh", 2), ("col", 0)]
    it "reports annotations that do not fit the datatype" $ do
        let derive annotations = void $ deriveLTAWith @SortedList 8 (atom @Integer LTAGen.every) annotations
        derive [("Cosn", mempty)] `shouldBe` Left (UnknownConstructors ["Cosn"] ["Nil", "Cons"])
        derive [("Cons", contract (\x -> x .<= 1))] `shouldBe` Left (AnnotationArityMismatch "Cons" (Arity 2) (Arity 1))
        derive [("Cons", measure (\x _ -> x) <> measure (\_ y -> y))] `shouldBe` Left (SeveralMeasures "Cons")
        derive [("Nil", contract (0 .<= (1 :: Expr)))] `shouldBe` Left (ContractWithoutFields "Nil")
        void (deriveLTAWith @SortedList 8 mempty []) `shouldSatisfy` either isMissingAtom (const False)
  where
    isMissingAtom (MissingAtom _) = True
    isMissingAtom _ = False
