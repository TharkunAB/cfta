{- | The data of a first-order many-sorted signature: the sorts, the function
symbols with their argument sorts and result sort, the root sorts, and the
sorts that have values. "Data.CFTA.Gen.ManySorted" reads a signature as a tree
automaton and as a generator, and checks it. The data is here, in @cfta@, so
that a package can print and read a signature without @cfta-generator@.
-}
module Data.CFTA.Signature (
    SortedSignature (..),
    SortedFunction (..),
    ValueSort (..),
    ValueSource (..),
) where

-- | A first-order many-sorted signature.
data SortedSignature sort symbol = SortedSignature
    { sortedSorts :: [sort]
    -- ^ The sorts. Every other sort in the signature must be in this list.
    , sortedFunctions :: [SortedFunction sort symbol]
    -- ^ The function symbols. Two functions must not have the same symbol.
    , sortedRoots :: [sort]
    -- ^ The sorts of the terms in the language.
    , sortedValues :: [ValueSort sort symbol]
    -- ^ The sorts that have values. A value is a leaf of size one.
    }
    deriving (Eq, Show)

-- | A sort with values. The values are leaves, so the sort can also have function symbols.
data ValueSort sort symbol = ValueSort
    { valueSort :: sort
    , valueSource :: ValueSource symbol
    }
    deriving (Eq, Show)

{- | The values of a sort. Neither kind lists its values: an interval of a
million integers costs the same as one integer.
-}
data ValueSource symbol
    = -- | The integers from the first bound to the second bound, both included.
      Interval !Integer !Integer
    | -- | Some symbols, in this order. Each symbol must occur once.
      Pool [symbol]
    deriving (Eq, Show)

-- | A function symbol with its argument sorts and its result sort.
data SortedFunction sort symbol = SortedFunction
    { functionSymbol :: symbol
    , functionArguments :: [sort]
    -- ^ The sorts of the arguments, from left to right. A constant has none.
    , functionResult :: sort
    }
    deriving (Eq, Show)
