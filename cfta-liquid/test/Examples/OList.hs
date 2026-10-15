{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

{- | The ordered lists of the Liquid Haskell test suite: the alias of
tests/pos/ListSort.hs, line 4, at 952f02cf of ucsd-progsys/liquidhaskell
(BSD-3-Clause), on the built-in list. The target alias @OListBounded@ is
added.
-}
module Examples.OList (derived) where

import Data.CFTA.Gen.Refinement.Derive (atom)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Liquid (LiquidError, deriveLTAFromLiquid)
import Data.CFTA.Liquid.TH (liquidSpecifications)

{-@ type OList a    = [a]<{\fld v -> (v >= fld)}> @-}

{-@ type OListBounded = OList {v:Integer | 0 <= v && v <= 1000000} @-}

-- | The derived ordered lists of the integers from zero to a million, of length up to eight.
derived :: Either LiquidError (LTAGen.LTAGen [Integer])
derived = deriveLTAFromLiquid @[Integer] 8 (atom @Integer LTAGen.every) $(liquidSpecifications) "OListBounded"
