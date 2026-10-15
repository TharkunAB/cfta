{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
-- The test suite's datatype has record fields in one of its two constructors.
{-# OPTIONS_GHC -Wno-partial-fields #-}

{- | The ordered red-black trees of the Liquid Haskell test suite: the
datatypes and the specifications of tests/pos/RBTree.hs (lines 7 to 28 and 138
to 205, at 952f02cf of ucsd-progsys/liquidhaskell, BSD-3-Clause). The function
signatures are left out. The deriving clauses, the alias @Key@ and the target
alias @BlackRootedORBT@ are added.
-}
module Examples.RBTree (RBTree (..), Color (..), keyCount, derived) where

import GHC.Generics (Generic)

import Data.CFTA.Gen.Refinement.Derive (atom)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Generic (HasFTA)
import Data.CFTA.Liquid (LiquidError, deriveLTAFromLiquid)
import Data.CFTA.Liquid.TH (liquidSpecifications)

-- | A red-black tree with keys.
data RBTree a
    = Leaf
    | Node
        { nCol :: Color
        , nKey :: a
        , nLeft :: !(RBTree a)
        , nRight :: !(RBTree a)
        }
    deriving stock (Show, Generic)
    deriving anyclass (HasFTA)

{-@ data RBTree a <l :: a -> a -> Bool, r :: a -> a -> Bool>
            = Leaf
            | Node { nCol   :: Color
                   , nKey   :: a
                   , nLeft  :: RBTree <l, r> (a <l nKey>)
                   , nRight :: RBTree <l, r> (a <r nKey>)
                  }
  @-}

-- | The color of a node.
data Color
    = -- | Black
      B
    | -- | Red
      R
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

{-@ type ORBT a = RBTree <{\root v -> v < root }, {\root v -> v > root}> a @-}

{-@ type RBT a    = {v: ORBT a | isRB v && isBH v } @-}

{-@ type RBTN a N = {v: RBT a  | bh v = N }         @-}

{-@ type ORBTL a X = RBT {v:a | v < X} @-}

{-@ type ORBTG a X = RBT {v:a | X < v} @-}

{-@ measure isRB        :: RBTree a -> Bool
      isRB Leaf         = true
      isRB (Node c x l r) = isRB l && isRB r && (c == R => (IsB l && IsB r))
  @-}

{-@ type ARBT a    = {v: ORBT a | isARB v && isBH v} @-}

{-@ type ARBTN a N = {v: ARBT a | bh v = N }         @-}

{-@ measure isARB        :: (RBTree a) -> Bool
      isARB Leaf         = true
      isARB (Node c x l r) = (isRB l && isRB r)
  @-}

{-@ type ARBT2 a L R = {v:ARBTN a {bh L} | (IsB L && IsB R) => isRB v} @-}

{-@ measure col         :: RBTree a -> Color
      col (Node c x l r)  = c
      col Leaf          = B
  @-}

{-@ measure isB        :: RBTree a -> Bool
      isB Leaf         = false
      isB (Node c x l r) = c == B
  @-}

{-@ predicate IsB T = not (col T == R) @-}

{-@ measure isBH        :: RBTree a -> Bool
      isBH Leaf         = true
      isBH (Node c x l r) = (isBH l && isBH r && bh l = bh r)
  @-}

{-@ measure bh        :: RBTree a -> Int
      bh Leaf         = 0
      bh (Node c x l r) = bh l + if (c == R) then 0 else 1
  @-}

{-@ predicate Invs V = Inv1 V && Inv2 V && Inv3 V   @-}

{-@ predicate Inv1 V = (isARB V && IsB V) => isRB V @-}

{-@ predicate Inv2 V = isRB V => isARB V            @-}

{-@ type Key = {v:Integer | 0 <= v && v < 5} @-}

{-@ type BlackRootedORBT = {v: RBT Key | IsB v && bh v <= 3} @-}

-- | The number of keys that the alias Key allows.
keyCount :: Integer
keyCount = 5

{- | The derived ordered red-black trees with a black root and a black height
of at most three. The keys are elements, not an 'LTAGen.every' range: the named
measures of a node, such as its least key, are one integer for each tuple of
children.
-}
derived :: Either LiquidError (LTAGen.LTAGen (RBTree Integer))
derived =
    deriveLTAFromLiquid @(RBTree Integer)
        6
        (atom @Integer $ LTAGen.elements [0 .. keyCount - 1])
        $(liquidSpecifications)
        "BlackRootedORBT"
