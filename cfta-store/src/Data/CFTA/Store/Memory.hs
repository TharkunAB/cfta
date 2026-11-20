-- | A store of revisions in memory. A process that ends loses the revisions.
module Data.CFTA.Store.Memory (
    newMemoryStore,
) where

import Data.IORef (atomicModifyIORef', newIORef, readIORef)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.CFTA.Serialization.Text (StateCodec)
import Data.CFTA.Store

-- | The revisions, and the children of each revision.
data Contents state = Contents
    { revisions :: !(Map RevisionId (Revision state))
    , childrenOf :: !(Map RevisionId (Set RevisionId))
    }

-- | An empty store.
newMemoryStore :: StateCodec state -> IO (Store state)
newMemoryStore codec = do
    ref <- newIORef $ Contents Map.empty Map.empty
    let get known = do
            contents <- readIORef ref
            pure $ maybe (Left $ UnknownRevision known) Right $ Map.lookup known (revisions contents)
        put new = atomicModifyIORef' ref $ \contents ->
            let known = revisionId new
             in case checkNew codec (`Map.member` revisions contents) new of
                    Left failure -> (contents, Left failure)
                    Right ()
                        | Map.member known (revisions contents) -> (contents, Right known)
                        | otherwise ->
                            ( Contents
                                (Map.insert known new (revisions contents))
                                (foldr (\parent -> Map.insertWith (<>) parent (Set.singleton known)) (childrenOf contents) (revisionParents new))
                            , Right known
                            )
    pure
        Store
            { storeCodec = codec
            , putRevision = put
            , getRevision = get
            , children = \known -> do
                contents <- readIORef ref
                pure $
                    if Map.member known (revisions contents)
                        then Right $ maybe [] Set.toAscList $ Map.lookup known (childrenOf contents)
                        else Left $ UnknownRevision known
            , ancestors = ancestorsVia get
            , listRevisions = Map.keys . revisions <$> readIORef ref
            }
