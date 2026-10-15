{-# LANGUAGE TypeFamilyDependencies #-}

{- | Refinements and measures written once, for values and for formulas.

A function that is polymorphic over 'Symbolic' runs on integers and gives a
'Bool', and it runs on the terms of "Data.CFTA.Refinement.Expression" and
gives a 'Formula'. So one definition is both a predicate on values and a
refinement:

@
inRange :: Symbolic e => e -> Truth e
inRange x = 0 .<= x .&& x .<= 1000000
@

@inRange (5 :: Integer)@ is 'True', and @inRange (variable "x")@ is the
formula @0 <= x && x <= 1000000@. The operators have the names and the
fixities of "Data.CFTA.Refinement.Expression". Import them from one of the
two modules.
-}
module Data.CFTA.Refinement.Symbolic (
    Boolean (..),
    Symbolic (..),
    Measures (..),
    NodeIntegers (..),
) where

import qualified Data.Kind as Kind
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)

import Data.CFTA.Formula (Formula)
import qualified Data.CFTA.Refinement.Expression as Expression

infix 4 .==, ./=, .<, .<=, .>, .>=
infixr 3 .&&
infixr 2 .||

-- | Truth values: 'Bool' for values, and 'Formula' for formulas.
class Boolean b where
    -- | The truth value that always holds.
    true :: b

    -- | The truth value that never holds.
    false :: b

    -- | Both hold.
    (.&&) :: b -> b -> b

    -- | At least one holds.
    (.||) :: b -> b -> b

    -- | The truth value does not hold.
    lnot :: b -> b

instance Boolean Bool where
    true = True
    false = False
    (.&&) = (&&)
    (.||) = (||)
    lnot = not

instance Boolean Formula where
    true = Expression.true
    false = Expression.false
    (.&&) = (Expression..&&)
    (.||) = (Expression..||)
    lnot = Expression.lnot

{- | Integers: 'Integer' for values, and 'Expression.Expr' for the terms of the
logic. 'Truth' is the type of a comparison.
-}
class (Num e, Boolean (Truth e)) => Symbolic e where
    -- | The truth values of the comparisons.
    type Truth e

    -- | The two integers are equal.
    (.==) :: e -> e -> Truth e

    -- | The two integers are different.
    (./=) :: e -> e -> Truth e

    -- | The first integer is less than the second.
    (.<) :: e -> e -> Truth e

    -- | The first integer is less than or equal to the second.
    (.<=) :: e -> e -> Truth e

    -- | The first integer is greater than the second.
    (.>) :: e -> e -> Truth e

    -- | The first integer is greater than or equal to the second.
    (.>=) :: e -> e -> Truth e

instance Symbolic Integer where
    type Truth Integer = Bool
    (.==) = (==)
    (./=) = (/=)
    (.<) = (<)
    (.<=) = (<=)
    (.>) = (>)
    (.>=) = (>=)

instance Symbolic Expression.Expr where
    type Truth Expression.Expr = Formula
    (.==) = (Expression..==)
    (./=) = (Expression../=)
    (.<) = (Expression..<)
    (.<=) = (Expression..<=)
    (.>) = (Expression..>)
    (.>=) = (Expression..>=)

{- | Integers whose children have named measures: 'Integer' for values, and
'Expression.Expr' for the terms of the logic. 'Child' is the type of a child
of a constructor: its term on 'Expression.Expr', and its integers,
'NodeIntegers', on 'Integer'. 'Child' determines the type of the integers, so
a condition such as @childMeasure "col" v .== 0@ needs no type annotation.

Write a helper that reads a measure as a function with an argument:

@
bh child = childMeasure "bh" child
@

A binding without an argument, @bh = childMeasure "bh"@, falls under the
monomorphism restriction. GHC then gives it one type of integers, and an
invariant cannot use it on both 'Expression.Expr' and 'Integer'.
-}
class (Symbolic e) => Measures e where
    -- | A child of a constructor. It determines the type of the integers.
    type Child e = (child :: Kind.Type) | child -> e

    -- | A named measure of a child, as in @childMeasure "bh" left@.
    childMeasure :: String -> Child e -> e

    -- | The integer of an atomic child.
    childValue :: Child e -> e

-- | On terms, a child is its term, and a named measure is an uninterpreted function of it.
instance Measures Expression.Expr where
    type Child Expression.Expr = Expression.Expr
    childMeasure name child = Expression.uninterpreted name [child]
    childValue = id

-- | On values, a child is the integers of a node.
instance Measures Integer where
    type Child Integer = NodeIntegers
    childMeasure name node =
        fromMaybe (error $ "Data.CFTA.Refinement.Symbolic: the child has no measure " <> name) $
            Map.lookup name (nodeMeasures node)
    childValue node = fromMaybe (error "Data.CFTA.Refinement.Symbolic: the child has no integer") $ nodeInteger node

-- | The integers of a node of a value: its integer, if it has one, and its named measures.
data NodeIntegers = NodeIntegers
    { nodeInteger :: !(Maybe Integer)
    , nodeMeasures :: !(Map.Map String Integer)
    }
    deriving (Eq, Show)
