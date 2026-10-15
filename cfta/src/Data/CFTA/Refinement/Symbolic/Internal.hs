{-# LANGUAGE TypeFamilyDependencies #-}

{- | The children of a constructor on values and on terms: the backend of the
derived refinement generators ("Data.CFTA.Gen.Refinement.Derive").

This module is exposed for integration, such as a translation that knows the
names of the measures only at run time. It is not part of the PVP contract.
A user of the derived generators reads the measures of a child with the
selectors of a record of measures, not with the strings of this module.
-}
module Data.CFTA.Refinement.Symbolic.Internal (
    Measures (..),
    NodeIntegers (..),
) where

import qualified Data.Kind as Kind
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)

import qualified Data.CFTA.Refinement.Expression as Expression
import Data.CFTA.Refinement.Symbolic (Symbolic)

{- | Integers whose children have named measures: 'Integer' for values, and
'Expression.Expr' for the terms of the logic. 'Child' is the type of a child
of a constructor: its term on 'Expression.Expr', and its integers,
'NodeIntegers', on 'Integer'. 'Child' determines the type of the integers.
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
        fromMaybe (error $ "Data.CFTA.Refinement.Symbolic.Internal: the child has no measure " <> name) $
            Map.lookup name (nodeMeasures node)
    childValue node = fromMaybe (error "Data.CFTA.Refinement.Symbolic.Internal: the child has no integer") $ nodeInteger node

-- | The integers of a node of a value: its integer, if it has one, and its named measures.
data NodeIntegers = NodeIntegers
    { nodeInteger :: !(Maybe Integer)
    , nodeMeasures :: !(Map.Map String Integer)
    }
    deriving (Eq, Show)
