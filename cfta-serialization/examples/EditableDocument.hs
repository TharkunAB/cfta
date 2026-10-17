{-# LANGUAGE OverloadedStrings #-}

-- | Reopen an editable language, remove facts, and change constructor rows.
module Main (main) where

import Control.Exception (bracketOnError, finally)
import qualified Data.ByteString.Lazy as ByteString
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Tree as Tree
import System.Directory (removeFile, renameFile)
import System.Environment (getArgs)
import System.FilePath (takeDirectory)
import System.IO (hClose, openBinaryTempFile)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Guard (Bottom, Satisfies), equalityConstraint, semanticConstraint)
import qualified Data.CFTA.Document as Document
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Path (path)
import Data.CFTA.Refinement.Expression (refinementFormula, (.==), (.>))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.CFTA.Serialization.Text (explainTextError, parseDocument, printDocument)
import qualified Data.CFTA.Sized as Sized
import Data.CFTA.Symbol (Symbol (RefinedSymbol), eraseRefinements)

-- | The source states use an exact derived label codec.
data State = Atom | Pair deriving (Eq, Ord, Show, Read)

-- | A named constant with its integer refinement and no transition facts.
atom :: String -> Symbol -> Integer -> FTA.Transition State Symbol Document.Annotation
atom name symbol value =
    FTA.Transition
        (RefinedSymbol symbol $ refinementFormula (.== fromInteger value))
        []
        (Document.Annotation (Text.pack name) Map.empty)

-- | Keep the disabled pair production in source so a later edit can restore it.
source :: Document.Document State
source =
    either (error . Document.explainDocumentError) id $
        Document.mkDocument
            Pair
            [
                ( Pair
                ,
                    [ FTA.Transition "pair" [Atom, Atom]
                        $ Document.Annotation "pair"
                        $ Map.fromList
                            [ ("same", equalityConstraint $ mkEqConstraints [[path [0], path [1]]])
                            , ("positive", semanticConstraint $ Satisfies (path [0]) $ refinementFormula (.> 0))
                            , ("disabled", semanticConstraint Bottom)
                            ]
                    ]
                )
            , (Atom, [atom "zero" "zero" 0, atom "one" "one" 1])
            ]

-- | Save the complete source document with atomic file replacement.
save :: FilePath -> Document.Document State -> IO ()
save target document =
    bracketOnError
        (openBinaryTempFile (takeDirectory target) ".cfta-document")
        (\(temporary, handle) -> hClose handle `finally` removeFile temporary)
        ( \(temporary, handle) -> do
            ByteString.hPut handle $ ByteString.fromStrict $ Text.encodeUtf8 $ printDocument document
            hClose handle
            renameFile temporary target
        )

-- | Read source facts without compiling them.
load :: FilePath -> IO (Document.Document State)
load sourceFile = do
    bytes <- ByteString.readFile sourceFile
    text <- either (fail . show) pure $ Text.decodeUtf8' $ ByteString.toStrict bytes
    either (fail . explainTextError) pure $ parseDocument text

-- | Show source facts and query the compiled language at size three.
inspect :: Document.Document State -> IO ()
inspect document = do
    putStr $ Tree.drawTree $ fmap (either show show) $ FTA.toTree $ Document.sourceGraph document
    withZ3 [] $ \solver -> do
        classes <- Sized.sizedUpTo solver 3 (Document.compileGraph document) >>= either (fail . show) pure
        print $ Sized.countOfSize classes 3
        print $ map eraseRefinements $ Sized.termsOfSize classes 3

-- | Remove two obligations and add one constructor in one validated patch.
edit :: Document.Document State -> Either (Document.DocumentError State) (Document.Document State)
edit before = Document.applyPatch changes before
  where
    changes =
        Document.patch
            before
            [ Document.RemoveFact Pair "pair" "disabled"
            , Document.RemoveFact Pair "pair" "positive"
            , Document.PutTransition Atom (atom "two" "two" 2)
            ]

-- | Run an in-memory example, or continue editing a saved source document.
main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        [] -> do
            reopened <- either (fail . explainTextError) pure $ parseDocument $ printDocument source
            inspect reopened
            either (fail . Document.explainDocumentError) inspect $ edit reopened
        ["save", target] -> save target source
        ["show", sourceFile] -> load sourceFile >>= inspect
        ["edit", sourceFile, target] -> do
            before <- load sourceFile
            after <- either (fail . Document.explainDocumentError) pure $ edit before
            save target after
        _ -> fail "usage: cfta-editable-document [save FILE | show FILE | edit INPUT OUTPUT]"
