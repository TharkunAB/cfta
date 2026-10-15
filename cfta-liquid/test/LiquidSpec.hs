{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

{- | Tests of "Data.CFTA.Liquid". The specifications of the Liquid Haskell
tutorial and test suite, as Liquid Haskell verifies them, give the
cardinality and the ranks of the hand-written generators of the examples:
SortedLists from the tutorial's IncList and from ListSort's OList, and
RedBlackTrees from RBTree_col_height. The ordered red-black trees of RBTree
have the counts that the red-black shapes and the choices of keys give.
SafeDivision and LiquidPairs come from the specifications of this module. The
translation rejects the specifications that it cannot translate exactly, with
their positions.
-}
module Main (main) where

-- A measure names each child, as in \leftHeight _ -> leftHeight, as a contract does.
{- HLINT ignore "Use const" -}
-- The specification of Division declares data, so the Haskell type is data too.
{- HLINT ignore "Use newtype instead of data" -}

import Control.Monad (forM_, unless, (>=>))
import Data.Containers.ListUtils (nubOrd)
import GHC.Generics (Generic)
import System.Directory (findExecutable)
import System.Exit (die)
import Test.Hspec (Expectation, Spec, describe, expectationFailure, hspec, it, shouldBe)

import Data.CFTA.Gen.Refinement.Derive (atom)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Generic (HasFTA)
import Data.CFTA.Index (Cardinality (..), Rank (..))
import Data.CFTA.Liquid (LiquidError (..), Specifications, deriveLTAFromLiquid, specifications)
import Data.CFTA.Liquid.TH (liquidSpecifications)
import Data.CFTA.Refinement.Expression (Refinement, (.&&), (./=), (.<), (.<=), (.==))

import qualified Examples.IncList as IncList
import qualified Examples.OList as OList
import qualified Examples.RBTree as Ordered
import qualified Examples.RBTreeColHeight as ColHeight

-- | The Liquid Haskell specifications of this module.
specs :: Specifications
specs = $(liquidSpecifications)

-- * Sorted lists

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

-- * Safe division

{-@ type Denominator = {v:Integer | 0 <= v && v <= 5 && v /= 0} @-}

{-@ data Division = Divide { d :: Denominator } @-}

-- | A division of twelve by a denominator.
data Division = Divide Integer
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | The derived divisions.
derivedDivisions :: Either LiquidError (LTAGen.LTAGen (Integer, Integer))
derivedDivisions =
    fmap (\(Divide denominator) -> (denominator, 12 `div` denominator))
        <$> deriveLTAFromLiquid @Division 0 (atom @Integer LTAGen.every) specs "Division"

-- | The hand-written divisions of SafeDivision.hs.
divisions :: LTAGen.LTAGen (Integer, Integer)
divisions = LTAGen.node "divide" $ LTAGen.do
    denominator <- LTAGen.elements [0 .. 5] `LTAGen.satisfying` (\v -> v ./= 0)
    LTAGen.pure (denominator, 12 `div` denominator)

-- * Liquid pairs

{-@ data Pair = Pair { left :: Integer, right :: {v:Integer | left < v} } @-}

-- | A pair of two values.
data Pair = Pair Integer Integer
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | Values that the solver knows only by the range that contains them.
ranged :: [(Integer, Refinement)]
ranged =
    [ (1, \v -> 0 .<= v .&& v .< 2)
    , (3, \v -> 2 .<= v .&& v .< 4)
    , (5, \v -> 4 .<= v .&& v .< 6)
    ]

-- | The derived pairs. The values come from the ranged pool.
derivedPairs :: Either LiquidError (LTAGen.LTAGen (Integer, Integer))
derivedPairs =
    fmap (\(Pair leftValue rightValue) -> (leftValue, rightValue))
        <$> deriveLTAFromLiquid @Pair 0 (atom @Integer (LTAGen.pool ranged)) specs "Pair"

-- | The hand-written pairs of LiquidPairs.hs.
pairs :: LTAGen.LTAGen (Integer, Integer)
pairs = LTAGen.guarded "pair" (\leftValue rightValue -> leftValue .< rightValue) $ LTAGen.do
    leftValue <- LTAGen.pool ranged
    rightValue <- LTAGen.pool ranged
    LTAGen.pure (leftValue, rightValue)

-- * Red-black trees

-- | The shape of a red-black tree, as in RedBlackTrees.hs.
data Tree = Leaf | Black Tree Tree | Red Tree Tree
    deriving (Eq, Show)

-- | The two-state generator of RedBlackTrees.hs: a black root and a black height of at most three.
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

-- | The shape of a tree of RBTree_col_height.
shapeOf :: ColHeight.RBTree () -> Tree
shapeOf ColHeight.Leaf = Leaf
shapeOf (ColHeight.Node ColHeight.B () l r) = Black (shapeOf l) (shapeOf r)
shapeOf (ColHeight.Node ColHeight.R () l r) = Red (shapeOf l) (shapeOf r)

{- | The counts of the hand-written trees by the number of internal nodes,
from zero to ten. A shape with n internal nodes has 2n + 1 nodes.
-}
shapeCounts :: IO [Integer]
shapeCounts = do
    compiled <- LTAGen.compile redBlackTrees
    pure [either (error . show) (\(Cardinality count) -> count) $ LTAGen.countAtSize compiled (2 * n + 1) | n <- [0 .. 10]]

{- | The counts of a derived generator by the number of internal nodes, from
zero to ten. A node of the datatypes of Liquid Haskell has a color and a key,
so a tree with n internal nodes has 4n + 1 nodes.
-}
derivedCounts :: LTAGen.LTAGen a -> IO [Integer]
derivedCounts generator = do
    compiled <- LTAGen.compile generator
    pure [either (error . show) (\(Cardinality count) -> count) $ LTAGen.countAtSize compiled (4 * n + 1) | n <- [0 .. 10]]

-- | Whether an ordered tree is a red-black tree with a black root, ordered keys, and keys in range.
validOrdered :: Ordered.RBTree Integer -> Bool
validOrdered tree =
    blackRoot
        && balanced tree
        && height tree <= 3
        && ordered (keys tree)
        && all (\key -> 0 <= key && key < Ordered.keyCount) (keys tree)
  where
    blackRoot = black tree
    keys Ordered.Leaf = []
    keys (Ordered.Node _ key l r) = keys l <> [key] <> keys r
    ordered xs = and (zipWith (<) xs (drop 1 xs))
    black (Ordered.Node Ordered.R _ _ _) = False
    black _ = True
    height Ordered.Leaf = 0 :: Int
    height (Ordered.Node color _ l _) = height l + (if color == Ordered.B then 1 else 0)
    balanced Ordered.Leaf = True
    balanced (Ordered.Node color _ l r) =
        balanced l && balanced r && height l == height r && (color == Ordered.B || (black l && black r))

-- | The binomial coefficient.
binomial :: Integer -> Integer -> Integer
binomial n k
    | k < 0 || k > n = 0
    | otherwise = product [n - k + 1 .. n] `div` product [1 .. k]

{- | Compile both generators, and expect the same cardinality and the same
value at each checked rank: every rank of a small generator, and the first
three, the middle, the last two, and 200 ranks of a fixed sequence of a large
one.
-}
sameRanks :: (Eq a, Show a) => LTAGen.LTAGen a -> Either LiquidError (LTAGen.LTAGen a) -> Expectation
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

-- | Expect a generator, and the validity of each of its members.
allValid :: (Show a) => (a -> Bool) -> Either LiquidError (LTAGen.LTAGen a) -> Expectation
allValid valid derived = case derived of
    Left err -> expectationFailure $ show err
    Right generator -> do
        compiled <- LTAGen.compile generator
        case LTAGen.cardinality compiled of
            Left err -> expectationFailure $ show err
            Right (Cardinality total) ->
                forM_ [0 .. total - 1] $ \rank -> case LTAGen.unrank compiled (Rank rank) of
                    Left err -> expectationFailure $ show err
                    Right member -> unless (valid member) $ expectationFailure $ "an invalid member: " <> show member

spec :: Spec
spec = describe "Data.CFTA.Liquid" $ do
    it "derives SortedLists from the IncList of the Liquid Haskell tutorial" $
        sameRanks sortedLists IncList.derived
    it "derives SortedLists from the OList of ListSort in the Liquid Haskell test suite" $
        sameRanks sortedLists OList.derived
    it "derives RedBlackTrees from RBTree_col_height in the Liquid Haskell test suite" $ do
        expected <- shapeCounts
        either (expectationFailure . show) (derivedCounts >=> (`shouldBe` expected)) ColHeight.derived
        sameRanks redBlackTrees (fmap shapeOf <$> ColHeight.derived)
    it "derives the ordered red-black trees of RBTree in the Liquid Haskell test suite" $ do
        shapes <- shapeCounts
        let expected = [count * binomial Ordered.keyCount n | (n, count) <- zip [0 ..] shapes]
        either (expectationFailure . show) (derivedCounts >=> (`shouldBe` expected)) Ordered.derived
        allValid validOrdered Ordered.derived
    it "derives SafeDivision from a data specification with a refinement alias" $
        sameRanks divisions derivedDivisions
    it "derives LiquidPairs from a data specification that relates two fields" $
        sameRanks pairs derivedPairs
    it "derives the sorted lists of a pool without bounds, with derived measures that say whether a list is empty" $
        allValid
            (\xs -> and (zipWith (<=) xs (drop 1 xs)) && length xs <= 3 && all (`elem` [0 .. 3]) xs)
            IncList.derivedUnbounded
    it "counts the sorted lists of a pool without bounds" $
        either
            (expectationFailure . show)
            (LTAGen.compile >=> (`shouldBe` Right (Cardinality $ binomial 7 3)) . LTAGen.cardinality)
            IncList.derivedUnbounded
    it "rejects a refinement of elements that is not an order relation" $
        deriveList [incList "IncList {v:a | v /= hd}"]
            `shouldBeError` Untranslatable
                "Rejected.hs:1:27: field tl of :<"
                "a refinement of elements that says v /= x needs the set of the elements"
    it "rejects a disjunction in a refinement of elements" $
        deriveList [incList "IncList {v:a | v < hd || v > hd}"]
            `shouldBeError` Untranslatable
                "Rejected.hs:1:27: field tl of :<"
                "the refinement of the elements is not a conjunction of linear order relations on v"
    it "rejects a product of two terms that are not constants" $
        deriveList [incList "IncList {v:a | hd * hd <= v}"]
            `shouldBeError` Untranslatable "Rejected.hs:1:27: field tl of :<" "a product of two terms that are not constants is not linear"
    it "rejects a name that is not a field" $
        deriveList [incList "IncList {v:a | y <= v}"]
            `shouldBeError` Untranslatable "Rejected.hs:1:27: field tl of :<" "y is not a field, a measure, or a predicate"
    it "rejects a measure that Liquid Haskell lifts from a Haskell function" $
        deriveList ["measure size", incList "{v:IncList a | size v < 3}"]
            `shouldBeError` Untranslatable
                "Rejected.hs:2:27: field tl of :<"
                "size is a measure that Liquid Haskell lifts from a Haskell function, and the translation reads the equations of a measure in its specification"
    it "rejects a measure that is not an integer" $
        deriveTree "Small" [keys, "type Small = {v: RBTree () | 0 < keys v}"]
            `shouldBeError` Untranslatable
                "Rejected.hs:1:12: the measure keys"
                "the measure gives a Set; a measure of a liquid tree automaton is an integer"
    it "rejects a measure without an equation for a constructor" $
        deriveTree "Small" [size, "type Small = {v: RBTree () | size v < 3}"]
            `shouldBeError` Untranslatable "Rejected.hs:1:12: the measure size" "the measure has no equation for Leaf"
    it "reports an unknown target" $
        deriveTree "Missing" ["type Small = RBTree ()"] `shouldBeError` UnknownTarget "Missing"
  where
    shouldBeError result expected = either Just (const Nothing) result `shouldBe` Just expected
    deriveList texts =
        deriveLTAFromLiquid @(IncList.IncList Integer) 4 (atom @Integer LTAGen.every) (rejected $ texts <> [bounded]) "Bounded"
    deriveTree target texts = deriveLTAFromLiquid @(ColHeight.RBTree ()) 2 mempty (rejected texts) target
    rejected texts = specifications [("Rejected.hs", line, 4, text) | (line, text) <- zip [1 ..] texts]
    bounded = "type Bounded = IncList {v:Integer | 0 <= v && v <= 9}"
    incList tailType = "data IncList a = Emp | (:<) { hd :: a, tl :: " <> tailType <> " }"
    keys =
        "measure keys :: RBTree a -> Set a\n        keys Leaf = Set_empty 0\n        keys (Node c x l r) = Set_cup (keys l) (keys r)"
    size = "measure size :: RBTree a -> Int\n        size (Node c x l r) = 1 + size l + size r"

main :: IO ()
main = do
    z3 <- findExecutable "z3"
    case z3 of
        Nothing -> die "The test suite needs the z3 executable on PATH; enter nix-shell or install Z3."
        Just _ -> pure ()
    hspec spec
