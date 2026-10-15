{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans -Wno-redundant-constraints #-}

{- | A category whose morphisms are maps between symbolic values of the
refinement logic.

'Sym' gives the symbolic value of a Haskell type: an integer type has an
'Expr', 'Bool' has a 'Formula', a pair has a pair, and a function has a
function. A morphism of 'FormulaCat' maps the symbolic value of its source to
the symbolic value of its target. The concat plugin gives the morphism of a
monomorphic Haskell function with @toCcc \@FormulaCat@. Then 'runFormulaCat'
applied to variables gives the formula of the function.

A curried predicate @Integer -> Integer -> Bool@ gives
@Expr -> Expr -> Formula@, which is the type of a contract, and
@Integer -> Bool@ gives a 'Data.CFTA.Refinement.Expression.Refinement'.

The category has instances for 'Integer', 'Int', 'Bool', @()@, pairs, and
functions. A list is an opaque 'Expr' that only the measures of
"Data.CFTA.Concat.Measure" read. Other types have no instances, so the plugin
cannot compile a function that uses them.
-}
module Data.CFTA.Concat.FormulaCat (
    Sym,
    FormulaCat (..),
) where

import Prelude hiding (const, curry, id, uncurry, (.))
import qualified Prelude

import Data.CFTA.Formula (Formula, Term (Div, Ite, Mod), iff)
import Data.CFTA.Refinement.Expression (
    Expr,
    false,
    fromExpr,
    lnot,
    toExpr,
    true,
    (.&&),
    (./=),
    (.<),
    (.<=),
    (.==),
    (.>),
    (.>=),
    (.||),
 )

import ConCat.AltCat
import qualified ConCat.Category

-- | The symbolic value of a Haskell type.
type family Sym a where
    Sym Integer = Expr
    Sym Int = Expr
    Sym Bool = Formula
    Sym () = ()
    Sym [a] = Expr
    Sym (a, b) = (Sym a, Sym b)
    Sym (a -> b) = Sym a -> Sym b

-- | A morphism from @a@ to @b@: a map from the symbolic value of @a@ to the symbolic value of @b@.
newtype FormulaCat a b = FormulaCat {runFormulaCat :: Sym a -> Sym b}

-- | The term that is the first term when the formula holds, and the second term when it does not.
conditional :: Formula -> Expr -> Expr -> Expr
conditional condition yes no = toExpr (Ite condition (fromExpr yes) (fromExpr no))

instance Category FormulaCat where
    id = FormulaCat Prelude.id
    FormulaCat g . FormulaCat f = FormulaCat (g Prelude.. f)
    {-# NOINLINE id #-}
    {-# NOINLINE (.) #-}

instance AssociativePCat FormulaCat where
    lassocP = FormulaCat (\(a, (b, c)) -> ((a, b), c))
    rassocP = FormulaCat (\((a, b), c) -> (a, (b, c)))
    {-# NOINLINE lassocP #-}
    {-# NOINLINE rassocP #-}

instance MonoidalPCat FormulaCat where
    FormulaCat f *** FormulaCat g = FormulaCat (\(a, b) -> (f a, g b))
    {-# NOINLINE (***) #-}

instance BraidedPCat FormulaCat where
    swapP = FormulaCat (\(a, b) -> (b, a))
    {-# NOINLINE swapP #-}

instance ProductCat FormulaCat where
    exl = FormulaCat fst
    exr = FormulaCat snd
    dup = FormulaCat (\a -> (a, a))
    {-# NOINLINE exl #-}
    {-# NOINLINE exr #-}
    {-# NOINLINE dup #-}

instance TerminalCat FormulaCat where
    it = FormulaCat (Prelude.const ())
    {-# NOINLINE it #-}

instance UnitCat FormulaCat where
    lunit = FormulaCat (\a -> ((), a))
    runit = FormulaCat (\a -> (a, ()))
    lcounit = FormulaCat snd
    rcounit = FormulaCat fst
    {-# NOINLINE lunit #-}
    {-# NOINLINE runit #-}
    {-# NOINLINE lcounit #-}
    {-# NOINLINE rcounit #-}

instance ClosedCat FormulaCat where
    apply = FormulaCat (\(f, a) -> f a)
    curry (FormulaCat f) = FormulaCat (\a b -> f (a, b))
    uncurry (FormulaCat g) = FormulaCat (\(a, b) -> g a b)
    {-# NOINLINE apply #-}
    {-# NOINLINE curry #-}
    {-# NOINLINE uncurry #-}

instance ConstCat FormulaCat () where
    const () = FormulaCat (Prelude.const ())
    {-# NOINLINE const #-}

instance ConstCat FormulaCat Bool where
    const b = FormulaCat (Prelude.const (if b then true else false))
    {-# NOINLINE const #-}

instance ConstCat FormulaCat Integer where
    const n = FormulaCat (Prelude.const (fromInteger n))
    {-# NOINLINE const #-}

instance ConstCat FormulaCat Int where
    const n = FormulaCat (Prelude.const (fromIntegral n))
    {-# NOINLINE const #-}

instance BoolCat FormulaCat where
    notC = FormulaCat lnot
    andC = FormulaCat (\(a, b) -> a .&& b)
    orC = FormulaCat (\(a, b) -> a .|| b)
    xorC = FormulaCat (\(a, b) -> lnot (iff a b))
    {-# NOINLINE notC #-}
    {-# NOINLINE andC #-}
    {-# NOINLINE orC #-}
    {-# NOINLINE xorC #-}

instance EqCat FormulaCat Bool where
    equal = FormulaCat (\(a, b) -> iff a b)
    notEqual = FormulaCat (\(a, b) -> lnot (iff a b))
    {-# NOINLINE equal #-}
    {-# NOINLINE notEqual #-}

instance EqCat FormulaCat Integer where
    equal = FormulaCat (\(a, b) -> a .== b)
    notEqual = FormulaCat (\(a, b) -> a ./= b)
    {-# NOINLINE equal #-}
    {-# NOINLINE notEqual #-}

instance EqCat FormulaCat Int where
    equal = FormulaCat (\(a, b) -> a .== b)
    notEqual = FormulaCat (\(a, b) -> a ./= b)
    {-# NOINLINE equal #-}
    {-# NOINLINE notEqual #-}

instance OrdCat FormulaCat Integer where
    lessThan = FormulaCat (\(a, b) -> a .< b)
    greaterThan = FormulaCat (\(a, b) -> a .> b)
    lessThanOrEqual = FormulaCat (\(a, b) -> a .<= b)
    greaterThanOrEqual = FormulaCat (\(a, b) -> a .>= b)
    {-# NOINLINE lessThan #-}
    {-# NOINLINE greaterThan #-}
    {-# NOINLINE lessThanOrEqual #-}
    {-# NOINLINE greaterThanOrEqual #-}

instance OrdCat FormulaCat Int where
    lessThan = FormulaCat (\(a, b) -> a .< b)
    greaterThan = FormulaCat (\(a, b) -> a .> b)
    lessThanOrEqual = FormulaCat (\(a, b) -> a .<= b)
    greaterThanOrEqual = FormulaCat (\(a, b) -> a .>= b)
    {-# NOINLINE lessThan #-}
    {-# NOINLINE greaterThan #-}
    {-# NOINLINE lessThanOrEqual #-}
    {-# NOINLINE greaterThanOrEqual #-}

instance MinMaxCat FormulaCat Integer where
    minC = FormulaCat (\(a, b) -> conditional (a .<= b) a b)
    maxC = FormulaCat (\(a, b) -> conditional (a .<= b) b a)
    {-# NOINLINE minC #-}
    {-# NOINLINE maxC #-}

instance MinMaxCat FormulaCat Int where
    minC = FormulaCat (\(a, b) -> conditional (a .<= b) a b)
    maxC = FormulaCat (\(a, b) -> conditional (a .<= b) b a)
    {-# NOINLINE minC #-}
    {-# NOINLINE maxC #-}

instance EnumCat FormulaCat Integer where
    succC = FormulaCat (+ 1)
    predC = FormulaCat (subtract 1)
    {-# NOINLINE succC #-}
    {-# NOINLINE predC #-}

instance EnumCat FormulaCat Int where
    succC = FormulaCat (+ 1)
    predC = FormulaCat (subtract 1)
    {-# NOINLINE succC #-}
    {-# NOINLINE predC #-}

instance NumCat FormulaCat Integer where
    negateC = FormulaCat negate
    addC = FormulaCat (\(a, b) -> a + b)
    subC = FormulaCat (\(a, b) -> a - b)
    mulC = FormulaCat (\(a, b) -> a * b)
    powIC = FormulaCat (Prelude.const (error "FormulaCat: the logic has no power"))
    {-# NOINLINE negateC #-}
    {-# NOINLINE addC #-}
    {-# NOINLINE subC #-}
    {-# NOINLINE mulC #-}
    {-# NOINLINE powIC #-}

instance NumCat FormulaCat Int where
    negateC = FormulaCat negate
    addC = FormulaCat (\(a, b) -> a + b)
    subC = FormulaCat (\(a, b) -> a - b)
    mulC = FormulaCat (\(a, b) -> a * b)
    powIC = FormulaCat (Prelude.const (error "FormulaCat: the logic has no power"))
    {-# NOINLINE negateC #-}
    {-# NOINLINE addC #-}
    {-# NOINLINE subC #-}
    {-# NOINLINE mulC #-}
    {-# NOINLINE powIC #-}

instance IntegralCat FormulaCat Integer where
    divC = FormulaCat (\(a, b) -> toExpr (Div (fromExpr a) (fromExpr b)))
    modC = FormulaCat (\(a, b) -> toExpr (Mod (fromExpr a) (fromExpr b)))
    {-# NOINLINE divC #-}
    {-# NOINLINE modC #-}

instance IntegralCat FormulaCat Int where
    divC = FormulaCat (\(a, b) -> toExpr (Div (fromExpr a) (fromExpr b)))
    modC = FormulaCat (\(a, b) -> toExpr (Mod (fromExpr a) (fromExpr b)))
    {-# NOINLINE divC #-}
    {-# NOINLINE modC #-}

instance FromIntegralCat FormulaCat Int Integer where
    fromIntegralC = FormulaCat Prelude.id
    {-# NOINLINE fromIntegralC #-}

instance FromIntegralCat FormulaCat Integer Int where
    fromIntegralC = FormulaCat Prelude.id
    {-# NOINLINE fromIntegralC #-}

instance IfCat FormulaCat Integer where
    ifC = FormulaCat (\(c, (a, b)) -> conditional c a b)
    {-# NOINLINE ifC #-}

instance IfCat FormulaCat Int where
    ifC = FormulaCat (\(c, (a, b)) -> conditional c a b)
    {-# NOINLINE ifC #-}

instance IfCat FormulaCat Bool where
    ifC = FormulaCat (\(c, (a, b)) -> (c .&& a) .|| (lnot c .&& b))
    {-# NOINLINE ifC #-}
