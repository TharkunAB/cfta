{-# LANGUAGE OverloadedStrings #-}

-- | The store of language revisions: identity, the DAG, merging, and the directory store.
module Main (main) where

import Control.Monad (forM_, when, (>=>))
import qualified Data.ByteString as ByteString
import Data.Either (isLeft)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import System.Directory (createDirectory, doesFileExist, listDirectory, removeDirectory, removeFile)
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.Hspec (Expectation, Spec, describe, expectationFailure, hspec, it, shouldBe, shouldReturn, shouldSatisfy)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalityConstraint, noConstraint)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Language (Language (..))
import qualified Data.CFTA.Language as L
import Data.CFTA.Language.Merge (Conflict (..), MergeError (..), Versions (..))
import qualified Data.CFTA.Language.Merge as Merge
import qualified Data.CFTA.Language.Source as D
import Data.CFTA.Path (path)
import Data.CFTA.Serialization.Text (StateCodec (..), parseCheckpoint, printCheckpoint, printLanguageWith)
import Data.CFTA.Sized.Checkpoint (resume, start)
import Data.CFTA.Store
import Data.CFTA.Store.Directory (openDirectory)
import Data.CFTA.Store.Memory (newMemoryStore)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Template (Exclusion (..), Template (..))

main :: IO ()
main = hspec $ do
    describe "the identity of a revision" identitySpec
    describe "the memory store" $ storeSpec (\use -> newMemoryStore codec >>= use)
    describe "the directory store" $ do
        storeSpec $ \use -> withSystemTempDirectory "cfta-store" (openedAt >=> use)
        directorySpec

-- | The codec of the revisions of the fixtures.
codec :: StateCodec String
codec = StateCodec Text.pack (Right . Text.unpack)

identitySpec :: Spec
identitySpec = do
    it "is the SHA-256 hash of the canonical text, whatever way the language was made" $ do
        -- The hash is that of @sha256sum@ on the text of 'printLanguageWith' of the base language.
        revisionIdText (revisionIdOf codec base) `shouldBe` "f14f7f40b71b5a1bc2cf42c17bf8cf61f137654be90bb9f83fdfbe43f7131fae"
        revisionIdOf codec (changed base $ leftChange <> rightChange)
            `shouldBe` revisionIdOf codec (changed base $ rightChange <> leftChange)
    it "differs for different languages" $
        revisionIdOf codec base `shouldSatisfy` (/= revisionIdOf codec (changed base leftChange))

-- | The laws of a store, for a way to make an empty one.
storeSpec :: ((Store String -> IO ()) -> IO ()) -> Spec
storeSpec withStore = do
    it "keeps a revision, and gives it back" $ withStore $ \store -> do
        root <- must =<< genesis store base (Map.fromList [("note", "line one\nline \"two\"")])
        found <- must =<< getRevision store root
        found `shouldBe` revision codec base [] Genesis (Map.fromList [("note", "line one\nline \"two\"")])
        revisionId found `shouldBe` root
        getRevision store (RevisionId "missing") `shouldReturnLeft` UnknownRevision (RevisionId "missing")
    it "does not change a revision that is put again, and shares the language of two branches" $ withStore $ \store -> do
        root <- must =<< genesis store base Map.empty
        viaLeft <- must =<< applyUpdate store root (leftChange <> rightChange)
        viaRight <- must =<< applyUpdate store root (rightChange <> leftChange)
        viaLeft `shouldBe` viaRight
        again <- must =<< putRevision store (revision codec base [viaLeft] Genesis (Map.fromList [("other", "metadata")]))
        again `shouldBe` root
        (revisionParents <$> (must =<< getRevision store root)) `shouldReturn` []
        (revisionOrigin <$> (must =<< getRevision store viaLeft)) `shouldReturn` Updated (leftChange <> rightChange)
    it "refuses a revision with an unknown parent, or with the wrong identity" $ withStore $ \store -> do
        root <- must =<< genesis store base Map.empty
        putRevision store (revision codec base [RevisionId "nobody"] Genesis Map.empty)
            `shouldReturnLeft` UnknownRevision (RevisionId "nobody")
        putRevision store (Revision root (changed base leftChange) [] Genesis Map.empty)
            `shouldReturnLeft` WrongId root (revisionIdOf codec (changed base leftChange))
    it "branches from one state with two edits, and merges them" $ withStore $ \store -> do
        root <- must =<< genesis store base Map.empty
        left <- must =<< applyUpdate store root leftChange
        right <- must =<< applyUpdate store root rightChange
        merged <- must =<< merge3 store root left right
        mergedState <- must =<< getRevision store merged
        Right (revisionLanguage mergedState)
            `shouldBe` either (Left . show) Right (mergeOf base (changed base leftChange) (changed base rightChange))
        revisionParents mergedState `shouldBe` [left, right]
        revisionOrigin mergedState `shouldBe` Merged root
        (must =<< children store root) `shouldReturn` sortedIds [left, right]
        (must =<< ancestors store merged) `shouldReturn` (sortedIds [left, right] <> [root])
        (must =<< ancestors store root) `shouldReturn` []
        (must =<< children store merged) `shouldReturn` []
        listRevisions store `shouldReturn` sortedIds [root, left, right, merged]
        -- A merge that has one side as its result is that side.
        (must =<< merge3 store root left root) `shouldReturn` left
    it "names the production of a conflict, and puts no state" $ withStore $ \store -> do
        root <- must =<< genesis store base Map.empty
        left <- must =<< applyUpdate store root leftChange
        right <- must =<< applyUpdate store root conflictingChange
        merge3 store root left right
            `shouldReturnLeft` MergeFailed
                ( Conflicts
                    [ ProductionConflict (L.at "s" "q") $
                        Versions
                            (productionOf "s" "q" base)
                            (productionOf "s" "q" $ changed base leftChange)
                            (productionOf "s" "q" $ changed base conflictingChange)
                    ]
                )
        (must =<< children store left) `shouldReturn` []
    it "reports an update that does not apply" $ withStore $ \store -> do
        root <- must =<< genesis store base Map.empty
        result <- applyUpdate store root (L.remove (L.at "nowhere" "p"))
        result `shouldSatisfy` isLeft

-- | Reopen, recover, and replay a directory store.
directorySpec :: Spec
directorySpec = do
    it "keeps its revisions, children, and ancestors when reopened" $
        withSystemTempDirectory "cfta-store" $ \directory -> do
            before <- openedAt directory
            root <- must =<< genesis before base Map.empty
            left <- must =<< applyUpdate before root leftChange
            right <- must =<< applyUpdate before root rightChange
            merged <- must =<< merge3 before root left right
            after <- openedAt directory
            forM_ [root, left, right, merged] $ \known ->
                (must =<< getRevision after known) `shouldReturnSame` (must =<< getRevision before known)
            (must =<< children after root) `shouldReturn` sortedIds [left, right]
            (must =<< ancestors after merged) `shouldReturn` (sortedIds [left, right] <> [root])
            names <- listDirectory (directory </> "revisions")
            length names `shouldBe` 4
    it "reads the parents from the revision files when a legacy index has the same keys" $
        withSystemTempDirectory "cfta-store" $ \directory -> do
            before <- openedAt directory
            root <- must =<< genesis before base Map.empty
            left <- must =<< applyUpdate before root leftChange
            writeFile (directory </> "index") $ unlines $ map (Text.unpack . revisionIdText) [root, left]
            reopened <- openedAt directory
            (must =<< children reopened root) `shouldReturn` [left]
    it "commits a revision without having to write a separate index" $
        withSystemTempDirectory "cfta-store" $ \directory -> do
            before <- openedAt directory
            root <- must =<< genesis before base Map.empty
            let index = directory </> "index"
            hasIndex <- doesFileExist index
            when hasIndex $ removeFile index
            createDirectory index
            left <- must =<< applyUpdate before root leftChange
            (must =<< children before root) `shouldReturn` [left]
            reopened <- openedAt directory
            (must =<< children reopened root) `shouldReturn` [left]
    it "does not publish a revision when renaming its file fails and can retry" $
        withSystemTempDirectory "cfta-store" $ \directory -> do
            store <- openedAt directory
            let root = revisionIdOf codec base
                target = directory </> "revisions" </> Text.unpack (revisionIdText root)
            createDirectory target
            failed <- genesis store base Map.empty
            failed `shouldSatisfy` either isStoreIO (const False)
            listRevisions store `shouldReturn` []
            removeDirectory target
            reopened <- openedAt directory
            listRevisions reopened `shouldReturn` []
            genesis reopened base Map.empty `shouldReturn` Right root
    it "finds a revision file that is not the hash of its language" $
        withSystemTempDirectory "cfta-store" $ \directory -> do
            store <- openedAt directory
            root <- must =<< genesis store base Map.empty
            let file = directory </> "revisions" </> Text.unpack (revisionIdText root)
                text = "cfta-revision 1\norigin genesis\n[language]\n" <> printLanguageWith codec (changed base leftChange)
            ByteString.writeFile file (Text.encodeUtf8 text)
            result <- getRevision store root
            result `shouldSatisfy` either isCorrupt (const False)
    it "resumes a size-ordered listing after reopening its revision" $
        withSystemTempDirectory "cfta-store" $ \directory -> do
            store <- openedAt directory
            root <- must =<< genesis store listed Map.empty
            known <- revisionLanguage <$> (must =<< getRevision store root)
            let graph = L.compileGraph known
                everything = either (error . show) id $ resume (start 4 [] graph) graph []
                cut = length everything `div` 3
                checkpointFile = directory </> "checkpoint"
            (length everything > 6) `shouldBe` True
            -- Save the checkpoint after listing some terms.
            writeFile checkpointFile $ Text.unpack $ printCheckpoint $ snd $ everything !! (cut - 1)
            -- Load the revision and the checkpoint from disk before resuming.
            after <- openedAt directory
            reloaded <- revisionLanguage <$> (must =<< getRevision after root)
            saved <- either (error . show) id . parseCheckpoint . Text.pack <$> readFile checkpointFile
            fmap (map fst) (resume saved (L.compileGraph reloaded) []) `shouldBe` Right (map fst $ drop cut everything)
  where
    isCorrupt failure = case failure of
        Corrupt _ _ -> True
        _ -> False
    isStoreIO failure = case failure of
        StoreIO _ -> True
        _ -> False
    shouldReturnSame actual expected = do
        a <- actual
        e <- expected
        a `shouldBe` e

-- | The base language of the tests.
base :: Language String
base =
    Language
        ( must' $
            D.mkDocument
                "s"
                [ ("s", [withFacts "p" "pair" ["a", "a"] [("f", noConstraint)], named "q" "wrap" ["s"]])
                , ("a", [named "r" "leaf" [], named "t" "one" [], named "v" "leaf" []])
                , ("b", [named "k" "leaf" []])
                ]
        )
        (Map.singleton "x" $ AtRoot Hole)

-- | A base language with no exclusion, whose listing has terms.
listed :: Language String
listed = changed base (L.restore "x")

-- | Two changes of different keys, and a change that conflicts with the first.
leftChange, rightChange, conflictingChange :: L.Update String
leftChange = L.define (L.at "s" "q") "wrap" ["a"]
rightChange = L.require (L.at "s" "p") "f" equal
conflictingChange = L.define (L.at "s" "q") "pair" ["s", "s"]

-- | The result of the merge of three languages.
mergeOf :: Language String -> Language String -> Language String -> Either (MergeError String) (Language String)
mergeOf = Merge.merge3

-- | Open the directory store.
openedAt :: FilePath -> IO (Store String)
openedAt directory = either (error . show) id <$> openDirectory codec directory

-- | Apply an update that must be valid.
changed :: Language String -> L.Update String -> Language String
changed language = must' . L.update language

-- | A production of a state by its name.
productionOf :: String -> D.ProductionName -> Language String -> Maybe (D.Production String)
productionOf state name language =
    lookup
        name
        [ (D.annotationName $ FTA.transitionConstraint p, p)
        | p <- concat $ Map.lookup state $ FTA.transitionTable $ D.sourceGraph $ L.source language
        ]

-- | A production without facts.
named :: D.ProductionName -> Symbol -> [String] -> D.Production String
named name symbol below = withFacts name symbol below []

-- | A production with facts.
withFacts :: D.ProductionName -> Symbol -> [String] -> [(D.FactName, Constraint)] -> D.Production String
withFacts name symbol below facts = FTA.Transition symbol below $ D.Annotation name $ Map.fromList facts

-- | A constraint that makes the two children equal.
equal :: Constraint
equal = equalityConstraint $ mkEqConstraints [[path [0], path [1]]]

-- | Identities in the order that the store gives them.
sortedIds :: [RevisionId] -> [RevisionId]
sortedIds = sort

-- | Stop a test on a store error.
must :: (Show failure) => Either failure value -> IO value
must = either (\failure -> fail (show failure)) pure

-- | Stop on an error in a fixture.
must' :: (Show failure) => Either failure value -> value
must' = either (error . show) id

-- | A store call that fails with this error.
shouldReturnLeft :: IO (Either (StoreError String) value) -> StoreError String -> Expectation
shouldReturnLeft action expected = action >>= either (`shouldBe` expected) (const $ expectationFailure "the call succeeded")
