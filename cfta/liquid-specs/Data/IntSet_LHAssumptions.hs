{-# OPTIONS_GHC -Wno-unused-imports #-}

{- | LiquidHaskell specifications of "Data.IntSet".

The plugin reads this module when a checked module imports "Data.IntSet".
LiquidHaskell does not check these specifications. They are assumptions.
-}
module Data.IntSet_LHAssumptions where

import Data.IntSet

-- The measures have no definition in the logic. So the logic knows only what
-- the specifications below say about them. Each specification below is true
-- for the definition that the comment on each measure gives.

-- The number of members of a set: intSetSize s is size s. The value for the
-- empty set is 0. No specification below gives a fact about the empty set.
{-@ measure intSetSize :: IntSet -> Int @-}

-- The largest member of a set: intSetMax s is findMax s, and the value for
-- the empty set is -9223372036854775808, which is minBound of a 64-bit Int.
-- The integers of the logic have no bounds, so for the logic this value is
-- only a number. No specification below gives a fact about the empty set.
-- With this value, the specification of union is also true when a set is
-- empty.
{-@ measure intSetMax :: IntSet -> Int @-}

{-@ assume singleton :: x:Int -> {v:IntSet | intSetSize v == 1 && intSetMax v == x} @-}

{-@ assume union :: a:IntSet -> b:IntSet -> {v:IntSet | intSetSize v <= intSetSize a + intSetSize b && (intSetMax v <= intSetMax a || intSetMax v <= intSetMax b)} @-}

-- The step function gets only members of the set. Each member is at most
-- intSetMax. Here q is a condition on the set and r is a condition on one
-- number. The constraint says that r holds for each number that is at most
-- intSetMax of a set with q. So r holds for each number that the step
-- function gets. The name is qualified, because the Prelude also exports
-- foldl'.
{-@ assume Data.IntSet.foldl' :: forall a <q :: IntSet -> Bool, r :: Int -> Bool>. {s :: IntSet<q>, x :: {x:Int | x <= intSetMax s} |- {v:Int | v == x} <: Int<r>} (a -> Int<r> -> a) -> a -> IntSet<q> -> a @-}
