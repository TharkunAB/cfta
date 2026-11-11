{-# OPTIONS_GHC -Wno-unused-imports #-}

{- | LiquidHaskell specifications of "Data.IntSet".

The plugin reads this module when a checked module imports "Data.IntSet".
LiquidHaskell does not check these specifications. They are assumptions.
-}
module Data.IntSet_LHAssumptions where

import Data.IntSet

-- The number of members of a set. The measure has no definition. So the
-- logic knows only what the specifications below say about it.
{-@ measure intSetSize :: IntSet -> Int @-}

{-@ assume singleton :: x:Int -> {v:IntSet | intSetSize v == 1} @-}

{-@ assume union :: a:IntSet -> b:IntSet -> {v:IntSet | intSetSize v <= intSetSize a + intSetSize b} @-}
