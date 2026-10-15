{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

{- | The red-black trees of the Liquid Haskell test suite, without the order of
the keys: the datatypes and the specifications of tests/pos/RBTree_col_height.hs
(lines 8 to 13 and 140 to 204, at 952f02cf of ucsd-progsys/liquidhaskell,
BSD-3-Clause). The function signatures are left out. The deriving clauses and
the target alias @BlackRootedRBT@ are added.
-}
module Examples.RBTreeColHeight (RBTree (..), Color (..), derived) where

import GHC.Generics (Generic)

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Generic (HasFTA)
import Data.CFTA.Liquid (LiquidError, deriveLTAFromLiquid)
import Data.CFTA.Liquid.TH (liquidSpecifications)

-- | A red-black tree.
data RBTree a
    = Leaf
    | Node Color a !(RBTree a) !(RBTree a)
    deriving stock (Show, Generic)
    deriving anyclass (HasFTA)

-- | The color of a node.
data Color
    = -- | Black
      B
    | -- | Red
      R
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

{-@ type RBT a    = {v: RBTree a | ((isRB v) && (isBH v)) } @-}

{-@ type RBTN a N = {v: (RBT a) | (bh v) = N }              @-}

{-@ measure isRB        :: RBTree a -> Bool
      isRB Leaf         = true
      isRB (Node c x l r) = ((isRB l) && (isRB r) && ((c == R) => ((IsB l) && (IsB r))))
  @-}

{-@ type ARBT a    = {v: RBTree a | ((isARB v) && (isBH v))} @-}

{-@ type ARBTN a N = {v: ARBT a   | (bh v) = N }             @-}

{-@ measure isARB        :: (RBTree a) -> Bool
      isARB Leaf         = true
      isARB (Node c x l r) = ((isRB l) && (isRB r))
  @-}

{-@ type ARBT2 a L R = {v:ARBTN a {(bh L)} | (((IsB L) && (IsB R)) => (isRB v))} @-}

{-@ measure col         :: RBTree a -> Color
      col (Node c x l r)  = c
      col Leaf          = B
  @-}

{-@ measure isB        :: RBTree a -> Bool
      isB Leaf         = false
      isB (Node c x l r) = c == B
  @-}

{-@ predicate IsB T = not ((col T) == R) @-}

{-@ measure isBH        :: RBTree a -> Bool
      isBH Leaf         = true
      isBH (Node c x l r) = ((isBH l) && (isBH r) && (bh l) = (bh r))
  @-}

{-@ measure bh        :: RBTree a -> Int
      bh Leaf         = 0
      bh (Node c x l r) = (bh l) + (if (c == R) then 0 else 1)
  @-}

{-@ predicate Invs V = ((Inv1 V) && (Inv2 V) && (Inv3 V))   @-}

{-@ predicate Inv1 V = (((isARB V) && (IsB V)) => (isRB V)) @-}

{-@ predicate Inv2 V = ((isRB V) => (isARB V))              @-}

{-@ predicate Inv3 V = 0 <= (bh V)                          @-}

{-@ invariant {v: Color | (v = R || v = B)}                 @-}

{-@ invariant {v: RBTree a | (Invs v)}                      @-}

{-@ type BlackRootedRBT = {v: RBT () | IsB v && bh v <= 3} @-}

-- | The derived red-black trees with a black root and a black height of at most three.
derived :: Either LiquidError (LTAGen.LTAGen (RBTree ()))
derived = deriveLTAFromLiquid @(RBTree ()) 6 mempty $(liquidSpecifications) "BlackRootedRBT"
