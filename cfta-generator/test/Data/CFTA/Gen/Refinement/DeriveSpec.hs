{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

{- | Tests of "Data.CFTA.Gen.Refinement.Derive": the derived generators of
SortedLists, SafeDivision, LiquidPairs, and RedBlackTrees have the cardinality
and the ranks of the hand-written generators of the examples, the typed
invariants give the annotations of the expression language byte for byte,
and a node view that does not fit its datatype is an error.
-}
module Data.CFTA.Gen.Refinement.DeriveSpec (spec) where

-- A measure names each child, as in \x _ -> x, as a contract does.
{- HLINT ignore "Use const" -}

import Control.Monad (forM_, void)
import Data.Containers.ListUtils (nubOrd)
import GHC.Generics (Generic)
import Test.Hspec (Expectation, Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)

import Data.CFTA.Gen.Refinement.Derive
import Data.CFTA.Gen.Refinement.Derive.Internal (
    Annotation,
    annotationFormulas,
    contract,
    deriveLTAWith,
    measure,
    measureNamed,
 )
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Generic (HasFTA)
import Data.CFTA.Index (Arity (..), Cardinality (..), Rank (..))
import Data.CFTA.Refinement.Expression (Expr, Formula, Refinement, uninterpreted)
import Data.CFTA.Refinement.Symbolic (Symbolic (..), true, (.&&))

-- | A list that its invariant keeps sorted.
data SortedList = Nil | Cons Integer SortedList
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | One node of a sorted list: an element, and the head of the rest.
data SortedListNode e = NilNode | ConsNode e e
    deriving stock (Generic)
    deriving anyclass (NodeView)

-- | The measure is the head. The head of the empty list is above every element.
instance HasLTA SortedList where
    type Node SortedList = SortedListNode
    type Measures SortedList = Single
    invariant = Measured headOf sorted

-- | The head of a sorted list.
headOf :: (Symbolic e) => SortedListNode e -> e
headOf NilNode = 1000001
headOf (ConsNode x _) = x

-- | Each element is from zero to a million, and at most the head of the rest.
sorted :: (Symbolic e) => SortedListNode e -> Truth e
sorted NilNode = true
sorted (ConsNode x restHead) = 0 .<= x .&& x .<= 1000000 .&& x .<= restHead

-- | A node view with one field too few for the constructor Cons.
data ShortNode e = ShortNil | ShortCons e
    deriving stock (Generic)
    deriving anyclass (NodeView)

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

-- | One node of a division: the denominator.
newtype DivisionNode e = DivideNode e
    deriving stock (Generic)
    deriving anyclass (NodeView)

-- | The denominator is from zero to five, and it is not zero.
instance HasLTA Division where
    type Node Division = DivisionNode
    invariant = Contracted (\(DivideNode d) -> 0 .<= d .&& d .<= 5 .&& d ./= 0)

-- | The hand-written divisions of SafeDivision.hs.
divisions :: LTAGen.LTAGen (Integer, Integer)
divisions = LTAGen.node "divide" $ LTAGen.do
    d <- LTAGen.elements [0 .. 5] `LTAGen.satisfying` (\v -> v ./= 0)
    LTAGen.pure (d, 12 `div` d)

-- | A pair whose left value is below its right value.
data Pair = Pair Integer Integer
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | One node of a pair: the two values.
data PairNode e = PairNode e e
    deriving stock (Generic)
    deriving anyclass (NodeView)

-- | The left value is below the right value.
instance HasLTA Pair where
    type Node Pair = PairNode
    invariant = Contracted (\(PairNode left right) -> left .< right)

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

-- | The measures of a tree: its black height and the color of its root.
data TreeMeasures e = TreeMeasures {bh :: e, col :: e}
    deriving stock (Eq, Show, Generic)
    deriving anyclass (MeasureRecord)

-- | One node of a tree: the measures of its children.
data TreeNode e
    = LeafNode
    | BlackNode (TreeMeasures e) (TreeMeasures e)
    | RedNode (TreeMeasures e) (TreeMeasures e)
    deriving stock (Generic)
    deriving anyclass (NodeView)

-- | The black height and the color of each tree, and the rules of red-black trees.
instance HasLTA Tree where
    type Node Tree = TreeNode
    type Measures Tree = TreeMeasures
    invariant = MeasuredBy measures balanced
      where
        measures LeafNode = TreeMeasures 0 0
        measures (BlackNode left _) = TreeMeasures (bh left + 1) 0
        measures (RedNode left _) = TreeMeasures (bh left) 1
        balanced LeafNode = true
        balanced (BlackNode left right) = bh left .== bh right
        balanced (RedNode left right) = bh left .== bh right .&& col left .== 0 .&& col right .== 0

-- | A node view of trees with integers in place of the records of measures.
data FlatTreeNode e = FlatLeaf | FlatBlack e e | FlatRed e e
    deriving stock (Generic)
    deriving anyclass (NodeView)

-- | The annotations of the red-black trees in the expression language, as the strings of the named measures gave them.
treeAnnotations :: [(String, Annotation)]
treeAnnotations =
    [ ("Leaf", measureNamed "bh" (0 :: Expr) <> measureNamed "col" (0 :: Expr))
    ,
        ( "Black"
        , contract (\left right -> bh' left .== bh' right)
            <> measureNamed "bh" (\left _ -> bh' left + 1)
            <> measureNamed "col" (\_ _ -> 0 :: Expr)
        )
    ,
        ( "Red"
        , contract (\left right -> bh' left .== bh' right .&& col' left .== 0 .&& col' right .== 0)
            <> measureNamed "bh" (\left _ -> bh' left)
            <> measureNamed "col" (\_ _ -> 1 :: Expr)
        )
    ]
  where
    bh' x = uninterpreted "bh" [x]
    col' x = uninterpreted "col" [x]

-- | The derived red-black trees: a black root and a black height of at most three.
derivedTrees :: Either DeriveLTAError (LTAGen.LTAGen Tree)
derivedTrees = (`LTAGen.satisfying` root) <$> deriveLTA @Tree 6 mempty
  where
    root v = col (measuresAt v) .== 0 .&& bh (measuresAt v) .<= 3

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
    it "gives the annotations of the expression language from the typed invariants, byte for byte" $ do
        let formulas annotations = [(name, annotationFormulas annotation) | (name, annotation) <- annotations]
            typed ::
                forall a node m.
                (HasFTA a, NodeView node) => Invariant node m -> Either DeriveLTAError [(String, ([Formula], [Expr], [(String, Expr)]))]
            typed rules = formulas <$> invariantAnnotations @a rules
            sortedListAnnotations = zip ["Nil", "Cons" :: String] (map snd listAnnotations)
        typed @SortedList (invariant @SortedList) `shouldBe` Right (formulas sortedListAnnotations)
        fmap show (typed @SortedList (invariant @SortedList)) `shouldBe` Right (show (formulas sortedListAnnotations))
        typed @Tree (invariant @Tree) `shouldBe` Right (formulas treeAnnotations)
        fmap show (typed @Tree (invariant @Tree)) `shouldBe` Right (show (formulas treeAnnotations))
        typed @Division (invariant @Division)
            `shouldBe` Right (formulas [("Divide", contract (\d -> 0 .<= d .&& d .<= 5 .&& d ./= (0 :: Expr)))])
        typed @Pair (invariant @Pair) `shouldBe` Right (formulas [("Pair", contract (\left right -> left .< (right :: Expr)))])
    it "reports a node view that does not fit its datatype" $ do
        let short = deriveLTAFrom @SortedList 8 (atom @Integer LTAGen.every) (Contracted (\_ -> true) :: Invariant ShortNode NoMeasures)
            flat =
                deriveLTAFrom @Tree 6 mempty (MeasuredBy (\_ -> TreeMeasures 0 0) (\_ -> true) :: Invariant FlatTreeNode TreeMeasures)
        void short `shouldBe` Left (NodeMismatch "Cons" "the constructor has 2 fields, the node view 1")
        void flat `shouldBe` Left (NodeMismatch "Black" "field 0 is Scalar in the node view, not Record [\"bh\",\"col\"]")
    it "checks values with the functions of the invariant" $ do
        let atoms = atom @Integer LTAGen.every
            rules = invariant @SortedList
        map (holds atoms rules) [Cons 1 (Cons 2 (Cons 2 Nil)), Cons 3 (Cons 1 Nil), Cons 2000000 Nil]
            `shouldBe` [True, False, False]
        map (measureOf atoms rules) [Cons 4 (Cons 5 Nil), Nil] `shouldBe` [4, 1000001]
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
            `shouldBe` TreeMeasures 2 0
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
