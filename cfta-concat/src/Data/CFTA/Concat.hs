{- | Refinements, contracts, and measures from monomorphic Haskell functions.

The concat plugin (Elliott, /Compiling to categories/, ICFP 2017) compiles a
monomorphic Haskell function with no recursion to the morphism of a
category. 'FormulaCat' is a category whose morphisms map the symbolic values
of the refinement logic, so the plugin gives the formula of a predicate and
the term of a measure. 'symbolic' gives the result in the types of the
refinement generators of "Data.CFTA.Gen.Refinement":

@
ordered :: Integer -> Integer -> Bool
ordered element restHead = element <= restHead
{\-# INLINE ordered #-\}

listHead :: Integer -> Integer -> Integer
listHead element _ = element
{\-# INLINE listHead #-\}

cons rest = LTAGen.measured "cons" (symbolic ordered) (symbolic listHead) ...
@

@symbolic ordered@ has the type @Expr -> Expr -> Formula@ of a contract,
@symbolic listHead@ has the type @Expr -> Expr -> Expr@ of a measure, and a
predicate @Integer -> Bool@ gives a 'Data.CFTA.Refinement.Expression.Refinement'.

A module that calls 'symbolic' must compile with the plugin and with
optimization: @-O -fplugin=ConCat.Plugin@. The function must be monomorphic,
it must have no recursion, and its definition must be visible to the plugin,
for example with an INLINE pragma. If the plugin cannot compile a call, the
call stays in the program and stops it when it runs. The plugin option
@-fplugin-opt=ConCat.Plugin:showResiduals@ lists such calls when the module
compiles, and a test that forces each formula finds them.
-}
module Data.CFTA.Concat (
    -- * Compiled predicates and measures
    symbolic,

    -- * The category
    Sym,
    FormulaCat (..),

    -- * Measures
    MeasureCat (..),
    len,
) where

import ConCat.AltCat (toCcc)

import Data.CFTA.Concat.FormulaCat (FormulaCat (..), Sym)
import Data.CFTA.Concat.Measure (MeasureCat (..), len)

{- | The symbolic version of a monomorphic Haskell function: its formula for a
predicate, and its term for a measure.

'symbolic' inlines, so that the plugin compiles the function in the module of
the call. That module must compile with @-O -fplugin=ConCat.Plugin@.
-}
symbolic :: (a -> b) -> Sym a -> Sym b
symbolic f = runFormulaCat (toCcc f)
{-# INLINE symbolic #-}
