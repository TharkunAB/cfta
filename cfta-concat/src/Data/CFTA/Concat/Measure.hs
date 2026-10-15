{-# OPTIONS_GHC -Wno-orphans #-}

{- | Uninterpreted measures as primitives of a category.

The concat plugin cannot compile a recursive function such as 'length'.
'len' is a primitive of the category instead. On @(->)@ it is 'length'. On
'FormulaCat' it is the uninterpreted measure @uninterpreted \"len\" [xs]@ of
the logic, as the measure @len@ of the Liquid synthesizer
("Data.CFTA.Gen.Synthesis.Liquid") is.

The plugin translates a function whose first type argument is the category
@(->)@. 'len' takes the category as its first type argument, and it inlines
only in the last phase of the simplifier, as the operations of
"ConCat.AltCat" do. So the plugin sees 'len' and not 'length'.

The plugin composes a morphism only on the types of the class
'ConCat.OkType.OkType'. This module has the orphan instance @OkType [a]@,
which makes a list an object of the category: a value that the category does
not take apart. Without the instance, the plugin unfolds 'len' to 'length',
and it cannot compile the recursion.
-}
module Data.CFTA.Concat.Measure (
    MeasureCat (..),
    len,
) where

import Data.CFTA.Refinement.Expression (uninterpreted)

import ConCat.OkType (OkType)

import Data.CFTA.Concat.FormulaCat (FormulaCat (..))

-- | A list is an object of the categories: the plugin does not take it apart.
instance OkType [a]

-- | Categories with the length of a list as a primitive.
class MeasureCat k where
    -- | The length of a list.
    lenC :: k [a] Int

instance MeasureCat (->) where
    lenC = length

instance MeasureCat FormulaCat where
    lenC = FormulaCat (\xs -> uninterpreted "len" [xs])
    {-# NOINLINE lenC #-}

-- | The length of a list, as a primitive of the category.
len :: (MeasureCat k) => k [a] Int
len = lenC
{-# INLINE [0] len #-}
