{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

{- | Tests of "Data.CFTA.Gen.Refinement.Derive": the derived generators of
SortedLists, SafeDivision, LiquidPairs, and RedBlackTrees have the cardinality
and the ranks of the hand-written generators of the examples, the typed
invariants give the annotations of the expression language byte for byte,
and a node view that does not fit its datatype is an error. Measures with a
choice give the binary search trees, the AVL trees, and the closed terms of
a language with let-binding that a plain predicate accepts.
-}
module Data.CFTA.Gen.Refinement.DeriveSpec (spec) where

-- A measure names each child, as in \x _ -> x, as a contract does.
{- HLINT ignore "Use const" -}

import Control.Monad (forM_, void)
import Data.Containers.ListUtils (nubOrd)
import Data.List (sort)
import Data.Maybe (isJust)
import Data.Proxy (Proxy (..))
import Data.Typeable (typeRep)
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
import Data.CFTA.Index (Arity (..), Cardinality (..), Depth, Rank (..))
import Data.CFTA.Refinement.Expression (Enumerated (..), Expr, Formula, Literal, Refinement, uninterpreted)
import Data.CFTA.Refinement.Lattice (latticeEntailment)
import Data.CFTA.Refinement.Symbolic (Symbolic (..), larger, smaller, true, (.&&))

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

-- | A binary search tree of keys.
data SearchTree = Tip | Bin SearchTree Integer SearchTree
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

{- | The measures of a search tree: its least and its greatest key. A 'Tip'
has the least key 4 and the greatest key -1, so that each key from 0 to 3
is between the bounds of an empty subtree.
-}
data Bounds e = Bounds {lo :: e, hi :: e}
    deriving stock (Eq, Show, Generic)
    deriving anyclass (MeasureRecord)

-- | One node of a search tree: the measures of the subtrees and the key.
data SearchTreeNode e = TipNode | BinNode (Bounds e) e (Bounds e)
    deriving stock (Generic)
    deriving anyclass (NodeView)

-- | The keys of the left subtree are less than the key, and the keys of the right subtree are greater.
instance HasLTA SearchTree where
    type Node SearchTree = SearchTreeNode
    type Measures SearchTree = Bounds
    invariant = MeasuredBy bounds ordered
      where
        bounds TipNode = Bounds 4 (-1)
        bounds (BinNode left key right) = Bounds (smaller (lo left) key) (larger (hi right) key)
        ordered TipNode = true
        ordered (BinNode left key right) = hi left .< key .&& key .< lo right

-- | Whether the keys of a search tree are in order.
isSearchTree :: SearchTree -> Bool
isSearchTree = ascending . keys
  where
    keys Tip = []
    keys (Bin left key right) = keys left <> [key] <> keys right
    ascending items = and (zipWith (<) items (drop 1 items))

-- | An AVL tree of keys.
data AVL = Empty | Branch AVL Integer AVL
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

-- | The measures of an AVL tree: its height, and its least and its greatest key.
data Shape e = Shape {height :: e, least :: e, greatest :: e}
    deriving stock (Eq, Show, Generic)
    deriving anyclass (MeasureRecord)

-- | One node of an AVL tree: the measures of the subtrees and the key.
data AVLNode e = EmptyNode | BranchNode (Shape e) e (Shape e)
    deriving stock (Generic)
    deriving anyclass (NodeView)

-- | The heights of the subtrees differ by at most one, and the keys are in order.
instance HasLTA AVL where
    type Node AVL = AVLNode
    type Measures AVL = Shape
    invariant = MeasuredBy shape balanced
      where
        shape EmptyNode = Shape 0 4 (-1)
        shape (BranchNode left key right) =
            Shape (1 + larger (height left) (height right)) (smaller (least left) key) (larger (greatest right) key)
        balanced EmptyNode = true
        balanced (BranchNode left key right) =
            abs (height left - height right) .<= 1 .&& greatest left .< key .&& key .< least right

-- | Whether the heights of the subtrees of each node differ by at most one, and the keys are in order.
isAVL :: AVL -> Bool
isAVL tree = maybe False (const (ascending (keys tree))) (heightOf tree)
  where
    heightOf Empty = Just (0 :: Int)
    heightOf (Branch left _ right) = do
        leftHeight <- heightOf left
        rightHeight <- heightOf right
        if abs (leftHeight - rightHeight) <= 1 then Just (1 + max leftHeight rightHeight) else Nothing
    keys Empty = []
    keys (Branch left key right) = keys left <> [key] <> keys right
    ascending items = and (zipWith (<) items (drop 1 items))

-- | A tree of keys whose measure is its height.
data Balanced = Stump | Fork Balanced Integer Balanced
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

-- | The height of a tree, as a named measure.
newtype Height e = Height {tall :: e}
    deriving stock (Eq, Show, Generic)
    deriving anyclass (MeasureRecord)

-- | One node of a tree: the heights of the subtrees and the key.
data BalancedNode e = StumpNode | ForkNode (Height e) e (Height e)
    deriving stock (Generic)
    deriving anyclass (NodeView)

{- | The heights of the subtrees differ by at most one. The greater height
comes from 'abs' and 'signum', which give a conditional term as 'ite' does.
-}
instance HasLTA Balanced where
    type Node Balanced = BalancedNode
    type Measures Balanced = Height
    invariant = MeasuredBy treeHeight balanced
      where
        treeHeight StumpNode = Height 0
        treeHeight (ForkNode left _ right) = Height (1 + greater (tall left) (tall right))
        greater a b = a + (b - a) * signum (b - a + abs (b - a))
        balanced StumpNode = true
        balanced (ForkNode left _ right) = abs (tall left - tall right) .<= 1

-- | Whether the heights of the subtrees of each node differ by at most one.
isBalanced :: Balanced -> Bool
isBalanced = isJust . heightOf
  where
    heightOf Stump = Just (0 :: Int)
    heightOf (Fork left _ right) = do
        leftHeight <- heightOf left
        rightHeight <- heightOf right
        if abs (leftHeight - rightHeight) <= 1 then Just (1 + max leftHeight rightHeight) else Nothing

-- | Terms with de Bruijn variables, a let, and a lambda.
data Scoped = Zero | Index Int | Plus Scoped Scoped | Let Scoped Scoped | Lambda Scoped
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

-- | One node of a term: the free-variable bounds of the subterms, and the index of a variable.
data ScopedNode e = ZeroNode | IndexNode e | PlusNode e e | LetNode e e | LambdaNode e
    deriving stock (Generic)
    deriving anyclass (NodeView)

{- | The measure is one more than the greatest free index, and 0 for a closed
term. A let binds one variable in its body, and so does a lambda.
-}
instance HasLTA Scoped where
    type Node Scoped = ScopedNode
    type Measures Scoped = Single
    invariant = Measured freeBound (const true)
      where
        freeBound ZeroNode = 0
        freeBound (IndexNode index) = index + 1
        freeBound (PlusNode left right) = larger left right
        freeBound (LetNode rhs body) = larger rhs (body - 1)
        freeBound (LambdaNode body) = larger 0 (body - 1)

-- | Whether each variable of a term is under a binder that binds it.
isClosed :: Scoped -> Bool
isClosed = go 0
  where
    go :: Int -> Scoped -> Bool
    go _ Zero = True
    go depth (Index index) = index < depth
    go depth (Plus left right) = go depth left && go depth right
    go depth (Let rhs body) = go depth rhs && go (depth + 1) body
    go depth (Lambda body) = go (depth + 1) body

{- | The number of closed terms up to the bound with the indices 0 to 3, from
a recurrence: @count n k@ is the number of terms whose free-variable bound
is at most @k@.
-}
closedCount :: Int -> Integer
closedCount bound = count bound 0
  where
    leaves k = 1 + fromIntegral (min k 4)
    count :: Int -> Int -> Integer
    count 0 k = leaves k
    count n k = leaves k + below k * below k + below k * below (k + 1) + below (k + 1)
      where
        below = count (n - 1)

-- | A shade, an enumeration that a field of a 'Tiles' value has.
data Shade = Light | Dark
    deriving stock (Eq, Ord, Show, Bounded, Enum, Generic)
    deriving anyclass (HasFTA)
    deriving (Literal) via (Enumerated Shade)

-- | A row of tiles.
data Tiles = NoTiles | Tile Shade Tiles
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

-- | One node of a row of tiles: the shade, and the number of dark tiles of the rest.
data TilesNode e = NoTilesNode | TileNode e e
    deriving stock (Generic)
    deriving anyclass (NodeView)

-- | The measure is the number of dark tiles: 'Dark' is 1.
instance HasLTA Tiles where
    type Node Tiles = TilesNode
    type Measures Tiles = Single
    invariant = Measured darkTiles (const true)
      where
        darkTiles NoTilesNode = 0
        darkTiles (TileNode shade rest) = shade + rest

-- | The measures of a sorted list for a condition on its length: the head and the length.
data ListMeasures e = ListMeasures {front :: e, size :: e}
    deriving stock (Eq, Show, Generic)
    deriving anyclass (MeasureRecord)

-- | One node of a sorted list, for named measures.
data SortedListByNode e = NilBy | ConsBy e (ListMeasures e)
    deriving stock (Generic)
    deriving anyclass (NodeView)

-- | The head and the length of a sorted list, as named measures.
byLength :: Invariant SortedListByNode ListMeasures
byLength = MeasuredBy measures (const true)
  where
    measures NilBy = ListMeasures 1000001 0
    measures (ConsBy x rest) = ListMeasures x (size rest + 1)

-- | The values of a datatype up to the bound, over the atoms, without an invariant, in order.
valuesUpTo :: forall a. (HasFTA a, Ord a) => Depth -> Atoms -> IO [a]
valuesUpTo bound atoms = membersOf $ deriveLTAFrom @a bound atoms (Contracted (const true) :: Invariant AnyNode NoMeasures)

-- | The members of a derived generator, in order.
membersOf :: (Ord a) => Either DeriveLTAError (LTAGen.LTAGen a) -> IO [a]
membersOf derived = do
    generator <- either (fail . show) LTAGen.compile derived
    either (fail . show) (pure . sort) (LTAGen.values generator)

{- | Expect the members of the derived generator to be the values of the
datatype up to the bound that the predicate accepts.
-}
sameMembers ::
    forall a.
    (HasFTA a, Ord a, Show a) => Depth -> Atoms -> (a -> Bool) -> Either DeriveLTAError (LTAGen.LTAGen a) -> Expectation
sameMembers bound atoms accepted derived = do
    expected <- filter accepted <$> valuesUpTo @a bound atoms
    membersOf derived >>= (`shouldBe` expected)

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
    it "derives search trees with key bounds from measures with a choice" $ do
        let keys = atom @Integer (LTAGen.elements [0 .. 3])
        sameMembers 3 keys isSearchTree (deriveLTA @SearchTree 3 keys)
        membersOf (deriveLTA @SearchTree 3 keys) >>= (`shouldBe` 43) . length
        measuresOf keys (invariant @SearchTree) (Bin (Bin Tip 0 Tip) 1 (Bin Tip 3 Tip)) `shouldBe` Bounds 0 3
    it "derives AVL trees whose measures compute the height" $ do
        let keys = atom @Integer (LTAGen.elements [0 .. 3])
        sameMembers 3 keys isAVL (deriveLTA @AVL 3 keys)
        membersOf (deriveLTA @AVL 3 keys) >>= (`shouldBe` 25) . length
        measuresOf keys (invariant @AVL) (Branch (Branch Empty 0 Empty) 1 Empty) `shouldBe` Shape 2 0 1
    it "derives height-balanced trees from a named measure with a conditional term" $
        sameMembers
            3
            (atom @Integer (LTAGen.elements [0, 1]))
            isBalanced
            (deriveLTA @Balanced 3 (atom @Integer (LTAGen.elements [0, 1])))
    it "derives the closed terms of a language with let-binding from a free-variable bound" $ do
        let indices = atom @Int (LTAGen.elements [0 .. 3])
            closed bound = (`LTAGen.satisfying` (.== 0)) <$> deriveLTA @Scoped bound indices
        sameMembers 2 indices isClosed (closed 2)
        compiled <- either (fail . show) LTAGen.compile (closed 3)
        LTAGen.cardinality compiled `shouldBe` Right (Cardinality (closedCount 3))
        map (measureOf indices (invariant @Scoped)) [Let Zero (Index 0), Lambda (Index 1), Plus (Index 2) Zero]
            `shouldBe` [0, 1, 3]
    it "names the measure and the child of an inexact named measure" $ do
        generator <- either (fail . show) pure $ deriveLTAFrom @SortedList 4 (atom @Integer LTAGen.every) byLength
        compiled <- LTAGen.compileWith latticeEntailment generator
        void compiled `shouldBe` Left (LTAGen.InexactMeasure "Cons" (Just "front") [0])
    it "reports a field whose type has no integer" $ do
        void (deriveLTA @Tiles 3 mempty) `shouldBe` Left (UnmeasuredField "Tile" 0 (typeRep (Proxy @Shade)))
        compiled <- either (fail . show) LTAGen.compile (deriveLTA @Tiles 2 (atom @Shade (LTAGen.elements [Light, Dark])))
        LTAGen.cardinality compiled `shouldBe` Right (Cardinality 7)
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
