{-# OPTIONS_GHC -Wno-unused-imports #-}

{- | LiquidHaskell specifications of "Data.IntMap.Strict".

The plugin reads this module when a checked module imports
"Data.IntMap.Strict". LiquidHaskell does not check these specifications.
They are assumptions.
-}
module Data.IntMap.Strict_LHAssumptions where

import Data.IntMap.Strict

-- The largest key of a map: intMapKeyMax m is the key of lookupMax m, and
-- the value for the empty map is -9223372036854775808, which is minBound of
-- a 64-bit Int. The measure has no definition in the logic. So the logic
-- knows only what the specifications below say about it. Each specification
-- below is true for this definition. The integers of the logic have no
-- bounds, so for the logic this value is only a number. Only the second
-- constraint of fromList uses the value for the empty map: the empty list
-- gives the empty map.
{-@ measure intMapKeyMax :: IntMap a -> Int @-}

{-@ assume insert :: k:Int -> x:a -> m:IntMap a -> {v:IntMap a | intMapKeyMax v <= intMapKeyMax m || intMapKeyMax v <= k} @-}

-- The largest key of the result is a key of the list, or minBound for the
-- empty list. Here r is a condition on one key and k is a condition on the
-- map. The first constraint says that k holds for each map whose largest key
-- has r. The second constraint says that k holds for each map whose largest
-- key is minBound. The parser does not accept a constraint without a binder,
-- so the second constraint binds d and does not use it. The specification
-- uses the number -9223372036854775808 and not minBound, so it is true for
-- this number with any size of Int.
{-@ assume fromList :: forall a <r :: Int -> Bool, k :: IntMap a -> Bool>. {x :: Int<r> |- {v:IntMap a | intMapKeyMax v == x} <: IntMap a <<k>>} {d :: Int |- {v:IntMap a | intMapKeyMax v == -9223372036854775808} <: IntMap a <<k>>} [(Int<r>, a)] -> IntMap a <<k>> @-}
