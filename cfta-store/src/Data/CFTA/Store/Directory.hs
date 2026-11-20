{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

{- | A store of revisions in a directory.

The directory has one text file for each revision in @revisions/@. The file
name is the revision ID.

> cfta-revision 1
> parent <identity>          (for each parent, in order)
> origin genesis | update | merged <identity>
> meta <(key, value) as shown>   (for each entry)
> [update]                   (only for the origin update)
> <the text of the update>
> [language]
> <the canonical text of the language>

The text after @[language]@ holds the language. The revision ID hashes its
canonical text. 'openDirectory' reads the revision files to build an in-memory
index of their parents. 'getRevision' checks the hash on each read. The store
trusts the parent links, origin, and metadata in those files.

A write publishes a revision by renaming a temporary file in the same
directory. Reopening skips any temporary files left by an interrupted write.
Use one open store handle per directory.
-}
module Data.CFTA.Store.Directory (
    openDirectory,
) where

import Control.Concurrent.MVar (MVar, modifyMVarMasked, newMVar, readMVar)
import Control.Exception (IOException, try)
import Control.Monad (unless)
import qualified Data.ByteString as ByteString
import Data.List (isSuffixOf)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import System.Directory (createDirectoryIfMissing, listDirectory, renameFile)
import System.FilePath ((</>))
import Text.Read (readMaybe)

import Data.CFTA.Serialization.Text (
    StateCodec,
    explainTextError,
    parseLanguageWith,
    parseUpdateWith,
    printLanguageWith,
    printUpdateWith,
 )
import Data.CFTA.Store

-- | The parents of each revision: the index of the store.
type Index = Map RevisionId [RevisionId]

{- | Open the store in a directory, and make the directory if it is not there.
The directory may have revisions of an earlier process.
-}
openDirectory :: (Ord state, Show state) => StateCodec state -> FilePath -> IO (Either (StoreError state) (Store state))
openDirectory codec directory = do
    made <- attempt $ createDirectoryIfMissing True (directory </> "revisions")
    case made of
        Left failure -> pure $ Left failure
        Right () -> do
            loaded <- loadIndex codec directory
            case loaded of
                Left failure -> pure $ Left failure
                Right index -> do
                    ref <- newMVar index
                    pure $ Right $ storeOf codec directory ref

storeOf :: (Ord state, Show state) => StateCodec state -> FilePath -> MVar Index -> Store state
storeOf codec directory ref =
    Store
        { storeCodec = codec
        , putRevision = put
        , getRevision = get
        , children = \known -> do
            index <- readMVar ref
            pure $
                if Map.member known index
                    then Right [child | (child, parents) <- Map.toList index, known `elem` parents]
                    else Left $ UnknownRevision known
        , ancestors = ancestorsVia get
        , listRevisions = Map.keys <$> readMVar ref
        }
  where
    get known = do
        index <- readMVar ref
        if Map.member known index then readRevision codec directory known else pure $ Left $ UnknownRevision known
    -- See Note [Publishing a revision].
    put new = modifyMVarMasked ref $ \index ->
        case checkNew codec (`Map.member` index) new of
            Left failure -> pure (index, Left failure)
            Right ()
                | Map.member known index -> pure (index, Right known)
                | otherwise -> do
                    let target = revisionFile directory known
                        temporary = target <> ".tmp"
                    written <- attempt $ do
                        ByteString.writeFile temporary $ Text.encodeUtf8 $ renderRevision codec new
                        renameFile temporary target
                    case written of
                        Left failure -> pure (index, Left failure)
                        Right () -> pure (Map.insert known (revisionParents new) index, Right known)
      where
        known = revisionId new

{- Note [Publishing a revision]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A put holds the index lock through the file rename and the index update.
If the write or rename fails, the index keeps its previous value. If the
process stops after the rename, the next open finds the published revision.
-}

-- | The file of a revision.
revisionFile :: FilePath -> RevisionId -> FilePath
revisionFile directory known = directory </> "revisions" </> Text.unpack (revisionIdText known)

-- | Run a file system action and report its failure as a store error.
attempt :: IO value -> IO (Either (StoreError state) value)
attempt action = either (\failure -> Left $ StoreIO $ show (failure :: IOException)) Right <$> try action

-- | The text of a revision file.
renderRevision :: StateCodec state -> Revision state -> Text
renderRevision codec current = header <> updateSection <> "[language]\n" <> printLanguageWith codec (revisionLanguage current)
  where
    header =
        Text.unlines $
            ["cfta-revision 1"]
                <> ["parent " <> revisionIdText parent | parent <- revisionParents current]
                <> [originLine (revisionOrigin current)]
                <> [ "meta " <> Text.pack (show (Text.unpack key, Text.unpack value)) | (key, value) <- Map.toList (revisionMetadata current)
                   ]
    updateSection = case revisionOrigin current of
        Updated change -> "[update]\n" <> Text.dropWhileEnd (== '\n') (printUpdateWith codec change) <> "\n"
        _ -> ""
    originLine origin = case origin of
        Genesis -> "origin genesis"
        Updated _ -> "origin update"
        Merged base -> "origin merged " <> revisionIdText base

-- | Read the parent edges from the revision files.
loadIndex :: (Ord state, Show state) => StateCodec state -> FilePath -> IO (Either (StoreError state) Index)
loadIndex codec directory = do
    listed <- attempt $ listDirectory (directory </> "revisions")
    case listed of
        Left failure -> pure $ Left failure
        Right names -> do
            let files = [RevisionId $ Text.pack name | name <- names, not (".tmp" `isSuffixOf` name)]
            build Map.empty files
  where
    build !index [] = pure $ Right index
    build !index (known : rest) = do
        loaded <- readRevision codec directory known
        case loaded of
            Left failure -> pure $ Left failure
            Right current -> build (Map.insert known (revisionParents current) index) rest

-- | Read a revision file, and check that its identity is the hash of its language.
readRevision ::
    (Ord state, Show state) =>
    StateCodec state -> FilePath -> RevisionId -> IO (Either (StoreError state) (Revision state))
readRevision codec directory known = do
    bytes <- attempt $ ByteString.readFile (revisionFile directory known)
    pure $ do
        content <- bytes
        text <- either (Left . Corrupt known . show) Right $ Text.decodeUtf8' content
        parsed <- either (Left . Corrupt known) Right $ parseRevision codec text
        let actual = revisionId parsed
        unless (actual == known) $ Left $ Corrupt known $ "the hash of the language is " <> Text.unpack (revisionIdText actual)
        pure parsed

-- | Parse the text of a revision file.
parseRevision :: (Ord state, Show state) => StateCodec state -> Text -> Either String (Revision state)
parseRevision codec text = do
    (headerAndUpdate, languageText) <- case Text.breakOn "[language]\n" text of
        (before, rest)
            | not (Text.null rest) && (Text.null before || "\n" `Text.isSuffixOf` before) ->
                Right (before, Text.drop (Text.length "[language]\n") rest)
        _ -> Left "no [language] section"
    let (headerText, updateSection) = Text.breakOn "[update]\n" headerAndUpdate
        headerLines = Text.lines headerText
    case headerLines of
        "cfta-revision 1" : fields -> do
            let parents = [RevisionId (Text.drop 7 field) | field <- fields, "parent " `Text.isPrefixOf` field]
                metadata = Map.fromList $ mapMaybe metaOf fields
            origin <- case [Text.drop 7 field | field <- fields, "origin " `Text.isPrefixOf` field] of
                ["genesis"] -> Right Genesis
                ["update"] ->
                    Updated
                        <$> (either (Left . explainTextError) Right . parseUpdateWith codec $ Text.drop (Text.length "[update]\n") updateSection)
                [merged] | Just base <- Text.stripPrefix "merged " merged -> Right $ Merged $ RevisionId base
                _ -> Left "no origin, or a bad origin"
            language <- either (Left . explainTextError) Right $ parseLanguageWith codec languageText
            Right $ revision codec language parents origin metadata
        _ -> Left "not a cfta-revision 1 file"
  where
    metaOf field = do
        entry <- Text.stripPrefix "meta " field
        (key, value) <- readMaybe (Text.unpack entry) :: Maybe (String, String)
        Just (Text.pack key, Text.pack value)
