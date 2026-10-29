{- | Saved positions in a size-ordered listing of the terms of a graph, and in
a sampled run of draws from that listing.

A checkpoint holds the language, the query, and the sized rank of the next
term. The language is a graph and its exclusions: the terms of the graph that
no exclusion rejects. The query is a route name, a route version, and a size
bound. The route and its version fix the order of the listing. The listing
holds the terms of the language of each size from one to the bound, in the
order of the route.

A sampling checkpoint holds the language, the query, the weights, the
pseudorandom generator (PRNG) and its seed, and the number of draws so far.
Each draw is a function of the seed and the index of the draw.

This module holds the data only. @Data.CFTA.Sized.Checkpoint@ of
@cfta-generator@ starts and resumes both kinds of checkpoint. The text forms
@checkpoint 1;@ and @sampling 1;@ of @cfta-serialization@ print and read them.
-}
module Data.CFTA.Checkpoint (
    Checkpoint (..),
    SamplingCheckpoint (..),
) where

import Data.Map.Strict (Map)
import Data.Text (Text)
import Data.Word (Word64)

import qualified Data.CFTA as FTA
import Data.CFTA.Index (ClassRank, Size, Weight)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Template (Exclusion)

{- | A saved position in a size-ordered listing of the terms of a language.

The graph and the exclusions are the identity of the checkpoint. A checkpoint
does not resume against another graph or other exclusions.
-}
data Checkpoint state = Checkpoint
    { checkpointGraph :: !(FTA.PlainFTA state Symbol)
    -- ^ The graph whose terms the query lists.
    , checkpointExclusions :: ![Exclusion Symbol]
    -- ^ The exclusions: the listing has the terms of the graph that none of them rejects.
    , checkpointRoute :: !Text
    -- ^ The name of the query route.
    , checkpointVersion :: !Integer
    -- ^ The version of the route. A new version can have a different order.
    , checkpointBound :: !Size
    -- ^ The largest size of a term in the listing.
    , checkpointNext :: !(Size, ClassRank)
    -- ^ The sized rank of the next term: its size and its class rank.
    }
    deriving (Eq, Show)

{- | A saved position in a sampled run: the draws of terms from the listing of
a language.

The graph, the exclusions, and the weights are the identity of the checkpoint.
A checkpoint does not resume against another graph, other exclusions, or other
weights.
-}
data SamplingCheckpoint state = SamplingCheckpoint
    { samplingGraph :: !(FTA.PlainFTA state Symbol)
    -- ^ The graph whose terms the run draws.
    , samplingExclusions :: ![Exclusion Symbol]
    -- ^ The exclusions: the run draws the terms of the graph that none of them rejects.
    , samplingRoute :: !Text
    -- ^ The name of the query route.
    , samplingVersion :: !Integer
    -- ^ The version of the route. A new version can draw other terms.
    , samplingBound :: !Size
    -- ^ The largest size of a term in the listing.
    , samplingWeights :: !(Maybe (Map Size Weight))
    -- ^ The weight of each size, or 'Nothing' for the same chance for each term of the listing.
    , samplingPrng :: !Text
    -- ^ The name of the pseudorandom generator.
    , samplingPrngVersion :: !Integer
    -- ^ The version of the pseudorandom generator.
    , samplingSeed :: !Word64
    -- ^ The seed of the run.
    , samplingDraws :: !Integer
    -- ^ The number of draws before the next draw.
    }
    deriving (Eq, Show)
