{- | Finite languages with stable ranks, independent of the sampling backend.

The generator layers of this package build on this module. A language is
compiled once. Then 'unrank', sampling, and shrinking read the compiled
language and not the automaton that it came from.

* t'Indexed' is a finite source: a cardinality and a decoder from a
  zero-based rank. "Data.CFTA.Index" defines t'Data.CFTA.Index.Rank' and
  t'Data.CFTA.Index.Cardinality'.

* t'WeightedIndexed' is a weighted finite source. It has a cardinality, a
  total weight, a decoder from a rank, and a map from a ticket to a rank.
  Each rank must have at least one ticket.

* t'RankedError' reports an empty language, a weight below one, a total
  weight below the cardinality, a negative rank, or a rank outside the
  language.

* t'GenBackend' is a sampling backend. It selects a rank below a
  cardinality, an 'Int' below a bound, one of several weighted generators,
  and one of several weighted values.

* t'Ranked' is a compiled language. This module does not export its
  constructor. It has 'Functor' and 'Applicative' instances.

* t'RankedValue' is a value with its rank. 'lowerWithRank' and
  'smallerMembers' give these.

The implementations are in "Data.CFTA.Ranked.Internal". The generator layers
of this package use that module directly.
-}
module Data.CFTA.Ranked (
    Indexed (..),
    WeightedIndexed (..),
    Ranked,
    RankedError (..),
    RankedValue (..),
    GenBackend (..),
    fromIndexed,
    fromIndexedOnDemand,
    fromWeightedIndexedOnDemand,
    fromWeighted,
    frequency,
    oneof,
    pay,
    cardinality,
    unrank,
    lower,
    lowerWithRank,
    shrinkRank,
    smallerMembers,
    sizeOfRank,
) where

import Data.CFTA.Index (Cardinality, Rank, Size, Weight)
import Data.CFTA.Ranked.Internal (Indexed (..), Ranked, RankedError (..), WeightedIndexed (..))
import qualified Data.CFTA.Ranked.Internal as Internal
import Data.CFTA.Ranked.Internal.Decoder (RankedValue (..))
import Data.CFTA.Ranked.Internal.Sampler (GenBackend (..))

-- | Build a ranked language from an indexed source.
fromIndexed :: Indexed a -> Either RankedError (Ranked a)
fromIndexed = Internal.fromIndexed

{- | Add one to the size of every member: the @pay@ of FEAT (Duregård, Jansson,
and Wang, Haskell Symposium 2012). Sizes count pays: 'pure' has size zero, an
indexed source has size one, and '<*>' adds the sizes of its sides. Ranks and
values do not change.
-}
pay :: Ranked a -> Ranked a
pay = Internal.pay

{- | Build a ranked language that decodes a member each time a caller reads it.

'fromIndexed' tabulates a source of at most 4096 members, so the decoder
keeps each member that it decodes. This function does not tabulate.
Automaton imports use it.
-}
fromIndexedOnDemand :: Indexed a -> Either RankedError (Ranked a)
fromIndexedOnDemand = Internal.fromIndexedOnDemand

{- | Build a weighted ranked language without enumerating its values or tickets.

Sampling selects one ticket and maps it to the retained replay rank. Weight
does not change cardinality or rank order. The constructor checks cardinality
and total weight only; it does not evaluate either callback.
-}
fromWeightedIndexedOnDemand :: WeightedIndexed a -> Either RankedError (Ranked a)
fromWeightedIndexedOnDemand = Internal.fromWeightedIndexedOnDemand

{- | Build a ranked language whose members have positive relative weights.

Weight affects sampling, not cardinality or rank order: each list entry has
exactly one stable rank.
-}
fromWeighted :: [(Weight, a)] -> Either RankedError (Ranked a)
fromWeighted = Internal.fromWeighted

-- | Combine non-empty alternatives with positive relative weights.
frequency :: [(Weight, Ranked a)] -> Either RankedError (Ranked a)
frequency = Internal.frequency

-- | Combine equally weighted non-empty alternatives.
oneof :: [Ranked a] -> Either RankedError (Ranked a)
oneof = Internal.oneof

-- | Return the exact number of stable ranks.
cardinality :: Ranked a -> Cardinality
cardinality = Internal.cardinality

-- | Decode one stable rank.
unrank :: Ranked a -> Rank -> Either RankedError a
unrank = Internal.unrank

-- | Lower a ranked language to any supported sampling backend.
lower :: (GenBackend gen) => Ranked a -> gen a
lower = Internal.lower

-- | Lower a ranked language while retaining the selected replay rank.
lowerWithRank :: (GenBackend gen) => Ranked a -> gen (RankedValue a)
lowerWithRank = Internal.lowerWithRank

{- | Structural shrink candidates for one rank.

Each candidate is a strictly smaller valid rank of the same language whose
member is no larger than the current member, measured in size.
Earlier alternatives come first at their smallest member, then each product
component shrinks on its own. Use 'smallerMembers' for every member of
strictly smaller size.
-}
shrinkRank :: Ranked a -> Rank -> [Rank]
shrinkRank = Internal.shrinkRank

-- | Every member structurally smaller than the selected member, in size order.
smallerMembers :: Ranked a -> Rank -> [RankedValue a]
smallerMembers = Internal.smallerMembers

-- | Structural size of the member at a valid rank.
sizeOfRank :: Ranked a -> Rank -> Maybe Size
sizeOfRank = Internal.sizeOfRank
