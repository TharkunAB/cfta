{-# LANGUAGE OverloadedStrings #-}

{- | Red-black trees with two named measures, the black height and the color,
in one recursive generator. Compare them with the two-state generator of
RedBlackTrees.hs.
-}
module Main (main) where

-- A measure names each child, as in \leftHeight _ -> leftHeight, as a contract does.
{- HLINT ignore "Use const" -}

import Control.Monad (unless)

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Refinement.Expression (Expr, uninterpreted, (.&&), (.<=), (.==))
import SameRanks (sameRanks)

-- | The shape of a red-black tree.
data Tree = Leaf | Black Tree Tree | Red Tree Tree
    deriving (Eq, Show)

-- | The black height of a tree.
bh :: Expr -> Expr
bh tree = uninterpreted "bh" [tree]

-- | The color of a tree: zero for black, one for red.
col :: Expr -> Expr
col tree = uninterpreted "col" [tree]

{- | Red-black trees with a black root and a black height of at most three. A
tree with this black height has at most six levels of internal nodes.
-}
measuredTrees :: LTAGen.LTAGen Tree
measuredTrees =
    LTAGen.recurUpTo 6 (\tree -> LTAGen.oneof [leaf, black tree, red tree])
        `LTAGen.satisfying` (\v -> col v .== 0 .&& bh v .<= 3)
  where
    leaf = LTAGen.leaf Leaf "leaf" (\v -> bh v .== 0 .&& col v .== 0)
    black child =
        LTAGen.measuredBy
            "black"
            (\left right -> bh left .== bh right)
            [("bh", \left _ -> bh left + 1), ("col", \_ _ -> 0)]
            (Black <$> child <*> child)
    red child =
        LTAGen.measuredBy
            "red"
            (\left right -> bh left .== bh right .&& col left .== 0 .&& col right .== 0)
            [("bh", \left _ -> bh left), ("col", \_ _ -> 1)]
            (Red <$> child <*> child)

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

-- | Compare the counts by size and the ranks.
main :: IO ()
main = do
    twoState <- LTAGen.compile redBlackTrees
    measured <- LTAGen.compile measuredTrees
    let sizes generator = [LTAGen.countAtSize generator (2 * n + 1) | n <- [0 .. 10]]
    unless (sizes twoState == sizes measured)
        $ fail
        $ "the counts by size differ: " <> show (sizes twoState) <> " and " <> show (sizes measured)
    putStrLn $ "counts by size agree: " <> show (sizes measured)
    sameRanks "RedBlackTrees with two measures" twoState measured
