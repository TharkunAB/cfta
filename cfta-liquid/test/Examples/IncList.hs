{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
-- The tutorial's datatype has record fields in one of its two constructors.
{-# OPTIONS_GHC -Wno-partial-fields #-}

{- | The ordered lists of the Liquid Haskell tutorial: the datatype and its
data specification of chapter 5 (src/Tutorial_05_Datatypes.lhs, lines 251 to
266, at 077437f3 of ucsd-progsys/liquidhaskell-tutorial, BSD-3-Clause). The
deriving clauses and the target alias @IncListBounded@ are added.
-}
module Examples.IncList (IncList (..), toList, derived, derivedUnbounded) where

import GHC.Generics (Generic)

import Data.CFTA.Gen.Refinement.Derive (atom)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Generic (HasFTA)
import Data.CFTA.Liquid (LiquidError, deriveLTAFromLiquid)
import Data.CFTA.Liquid.TH (liquidSpecifications)

-- | A list whose specification keeps it ordered.
data IncList a
    = Emp
    | (:<) {hd :: a, tl :: IncList a}
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

infixr 9 :<

{-@ data IncList a =
        Emp
      | (:<) { hd :: a, tl :: IncList {v:a | hd <= v}}  @-}

{-@ type IncListBounded = IncList {v:Integer | 0 <= v && v <= 1000000} @-}

-- | The elements of a list.
toList :: IncList a -> [a]
toList Emp = []
toList (x :< rest) = x : toList rest

-- | The derived ordered lists of the integers from zero to a million, of length up to eight.
derived :: Either LiquidError (LTAGen.LTAGen [Integer])
derived =
    fmap toList
        <$> deriveLTAFromLiquid @(IncList Integer) 8 (atom @Integer LTAGen.every) $(liquidSpecifications) "IncListBounded"

{- | The derived ordered lists of the integers from zero to three, of length up
to three. The target has no bound on the elements, so the derived measures of
a list say whether it is empty.
-}
derivedUnbounded :: Either LiquidError (LTAGen.LTAGen [Integer])
derivedUnbounded =
    fmap toList
        <$> deriveLTAFromLiquid @(IncList Integer) 3 (atom @Integer $ LTAGen.elements [0 .. 3]) $(liquidSpecifications) "IncList"
