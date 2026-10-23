{- | A saved position in a size-ordered listing of the terms of a graph.

A checkpoint holds the graph, the query, and the sized rank of the next term.
The query is a route name, a route version, and a size bound. The route and
its version fix the order of the listing. The listing holds the terms of each
size from one to the bound, in the order of the route.

This module holds the data only. @Data.CFTA.Sized.Checkpoint@ of
@cfta-generator@ starts, resumes, and relocates a checkpoint. The text form
@checkpoint 1;@ of @cfta-serialization@ prints and reads it.
-}
module Data.CFTA.Checkpoint (
    Checkpoint (..),
) where

import Data.Text (Text)

import qualified Data.CFTA as FTA
import Data.CFTA.Index (ClassRank, Size)
import Data.CFTA.Symbol (Symbol)

{- | A saved position in a size-ordered listing of the terms of a graph.

The graph is the identity of the checkpoint. A checkpoint does not resume
against another graph.
-}
data Checkpoint state = Checkpoint
    { checkpointGraph :: !(FTA.PlainFTA state Symbol)
    -- ^ The graph whose terms the query lists.
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
