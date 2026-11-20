{-# LANGUAGE OverloadedStrings #-}

{- | A content-addressed store of language revisions.

A 'Revision' is a language with its parents, its origin, and its
metadata. Its 'RevisionId' is the SHA-256 hash of the UTF-8 canonical language
text from 'Data.CFTA.Serialization.Text.printLanguageWith' and the store's
state codec. Equal languages have one identity. The identity covers the
language alone.

__The DAG.__ A revision names its parents, and each parent is in the store before
the revision is. So the revisions form a DAG, and no revision is its own ancestor. A
revision that is put again, whatever its parents, is not changed: the first put
wins, and 'putRevision' gives the identity of the revision. So two branches
that make the same language share one revision, with the parents of the branch
that came first.

__The port.__ A 'Store' is a record of functions: the codec, 'putRevision',
'getRevision', 'children', 'ancestors', and 'listRevisions'. 'applyUpdate' and 'merge3' use only
these, so they work for every store. 'Data.CFTA.Store.Memory' and
'Data.CFTA.Store.Directory' make stores.

__Merging.__ 'merge3' gives the revision of 'Data.CFTA.Language.Merge.merge3' of three
revisions. A conflict names the key, a production, a fact, a state, or an
exclusion, with the three versions, as 'Data.CFTA.Language.Merge' does.
-}
module Data.CFTA.Store (
    RevisionId (..),
    Revision (..),
    Origin (..),
    StoreError (..),
    Store (..),
    revision,
    revisionIdOf,
    sha256Hex,
    genesis,
    applyUpdate,
    merge3,
    ancestorsVia,
    checkNew,
    explainStoreError,
) where

import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString as ByteString
import Data.List (nub, sort)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Numeric (showHex)

import qualified Data.CFTA.Language as L
import qualified Data.CFTA.Language.Merge as Merge
import Data.CFTA.Serialization.Text (StateCodec, printLanguageWith)

{- | The identity of a revision: the SHA-256 hash of the canonical text of its
language, as 64 hexadecimal digits.
-}
newtype RevisionId = RevisionId {revisionIdText :: Text}
    deriving (Eq, Ord, Show)

-- | How a revision was made.
data Origin state
    = -- | A revision with no parent.
      Genesis
    | -- | The update of the one parent.
      Updated !(L.Update state)
    | -- | The merge of the two parents, from this base.
      Merged !RevisionId
    deriving (Eq, Show)

-- | A language with its place in the DAG.
data Revision state = Revision
    { revisionId :: !RevisionId
    , revisionLanguage :: !(L.Language state)
    , revisionParents :: ![RevisionId]
    , revisionOrigin :: !(Origin state)
    , revisionMetadata :: !(Map Text Text)
    }
    deriving (Eq, Show)

-- | Why a store call fails.
data StoreError state
    = -- | No revision has this identity.
      UnknownRevision !RevisionId
    | -- | The given revision ID differs from the hash of its language.
      WrongId !RevisionId !RevisionId
    | -- | An update that does not apply to the language of a revision.
      UpdateFailed !(L.UpdateError state)
    | -- | A merge with conflicts, or a merge that is not a valid document.
      MergeFailed !(Merge.MergeError state)
    | -- | A revision that cannot be read: the identity and the reason.
      Corrupt !RevisionId !String
    | -- | A failure of the file system.
      StoreIO !String
    deriving (Eq, Show)

{- | A store of revisions. The calls report their failures and do not throw
them.

* 'putRevision' stores a revision whose parents are in the store, and whose
  identity is the hash of its language. A revision that is in the store already
  is not changed.
* 'children' gives the revisions that name the revision as a parent, in the order of
  their identities.
* 'ancestors' gives the proper ancestors of a revision, the nearest first (by
  the length of the shortest path), and by identity among those at one distance.
  Each is once.
* 'listRevisions' gives the identities of all revisions, in the order of the identities.
-}
data Store state = Store
    { storeCodec :: StateCodec state
    , putRevision :: Revision state -> IO (Either (StoreError state) RevisionId)
    , getRevision :: RevisionId -> IO (Either (StoreError state) (Revision state))
    , children :: RevisionId -> IO (Either (StoreError state) [RevisionId])
    , ancestors :: RevisionId -> IO (Either (StoreError state) [RevisionId])
    , listRevisions :: IO [RevisionId]
    }

-- | The identity of a language: the hash of its canonical text.
revisionIdOf :: StateCodec state -> L.Language state -> RevisionId
revisionIdOf codec language = RevisionId $ sha256Hex $ printLanguageWith codec language

-- | The SHA-256 hash of the UTF-8 encoding of a text, as 64 hexadecimal digits.
sha256Hex :: Text -> Text
sha256Hex = Text.pack . concatMap hex . ByteString.unpack . SHA256.hash . Text.encodeUtf8
  where
    hex byte = (if byte < 16 then "0" else "") <> showHex byte ""

-- | A revision with its identity.
revision ::
    StateCodec state -> L.Language state -> [RevisionId] -> Origin state -> Map Text Text -> Revision state
revision codec language = Revision (revisionIdOf codec language) language

-- | Put a revision with no parent.
genesis :: Store state -> L.Language state -> Map Text Text -> IO (Either (StoreError state) RevisionId)
genesis store language metadata = putRevision store $ revision (storeCodec store) language [] Genesis metadata

{- | Apply an update to a revision and put the result as a child. When another
branch made the same language already, the result is that revision.
-}
applyUpdate :: (Ord state) => Store state -> RevisionId -> L.Update state -> IO (Either (StoreError state) RevisionId)
applyUpdate store base change = either (pure . Left) apply =<< getRevision store base
  where
    apply parent = case L.update (revisionLanguage parent) change of
        Left failure -> pure $ Left $ UpdateFailed failure
        Right language ->
            putRevision store $ revision (storeCodec store) language [base] (Updated change) Map.empty

{- | Merge two revisions that come from one base, as 'Data.CFTA.Language.Merge.merge3'
does, and put the result as a child of both. When the merge is the left or
the right revision, the result is that revision.
-}
merge3 ::
    (Ord state) => Store state -> RevisionId -> RevisionId -> RevisionId -> IO (Either (StoreError state) RevisionId)
merge3 store base left right = do
    versions <- traverse (getRevision store) [base, left, right]
    either (pure . Left) merge (sequence versions)
  where
    merge versions = case map revisionLanguage versions of
        [baseLanguage, leftLanguage, rightLanguage] -> case Merge.merge3 baseLanguage leftLanguage rightLanguage of
            Left failure -> pure $ Left $ MergeFailed failure
            Right language -> putRevision store $ revision (storeCodec store) language (nub [left, right]) (Merged base) Map.empty
        _ -> pure $ Left $ StoreIO "merge3: not three revisions"

{- | The proper ancestors of a revision, the nearest first, each once, from a
function that gives a revision. A store can use it for 'ancestors'.
-}
ancestorsVia ::
    (Monad m) =>
    (RevisionId -> m (Either (StoreError state) (Revision state))) ->
    RevisionId ->
    m (Either (StoreError state) [RevisionId])
ancestorsVia get start = go [] [start]
  where
    go found [] = pure $ Right found
    go found level = do
        loaded <- traverse get level
        case sequence loaded of
            Left failure -> pure $ Left failure
            Right revisions ->
                let new =
                        sort $ nub [parent | current <- revisions, parent <- revisionParents current, parent `notElem` found, parent /= start]
                 in go (found <> new) new

{- | Check a revision before it is put, for the code of a store: its identity is the
hash of its language, and its parents are in the store.
-}
checkNew :: StateCodec state -> (RevisionId -> Bool) -> Revision state -> Either (StoreError state) ()
checkNew codec known new
    | actual /= revisionId new = Left $ WrongId (revisionId new) actual
    | otherwise = case filter (not . known) (revisionParents new) of
        missing : _ -> Left $ UnknownRevision missing
        [] -> Right ()
  where
    actual = revisionIdOf codec (revisionLanguage new)

-- | Describe a store error.
explainStoreError :: (Show state) => StoreError state -> String
explainStoreError failure = case failure of
    UnknownRevision (RevisionId known) -> "no revision " <> Text.unpack known
    WrongId (RevisionId given) (RevisionId actual) -> "revision " <> Text.unpack given <> " has the hash " <> Text.unpack actual
    UpdateFailed failure' -> "the update does not apply: " <> show failure'
    MergeFailed failure' -> "the merge fails: " <> show failure'
    Corrupt (RevisionId known) reason -> "revision " <> Text.unpack known <> " cannot be read: " <> reason
    StoreIO reason -> reason
