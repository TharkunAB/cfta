{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Compose language updates in memory, then save, reopen, and restore an exclusion.
module Main (main) where

import Data.Aeson (FromJSON, ToJSON)
import GHC.Generics (Generic)

import Control.Exception (bracketOnError, finally)
import qualified Data.ByteString.Lazy as ByteString
import qualified Data.Map.Strict as Map
import qualified Data.Text.Encoding as Text
import System.Directory (removeFile, renameFile)
import System.Environment (getArgs)
import System.FilePath (takeDirectory)
import System.IO (hClose, openBinaryTempFile)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Guard (Bottom, Satisfies), equalityConstraint, semanticConstraint)
import qualified Data.CFTA.Document as Document
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import qualified Data.CFTA.Language as Language
import Data.CFTA.Path (path)
import Data.CFTA.Refinement.Expression (refinementFormula, (.==), (.>))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.CFTA.Serialization.JSON (decodeLanguage, encodeLanguage, explainDecodeError)
import qualified Data.CFTA.Serialization.Text as LanguageText
import qualified Data.CFTA.Sized as Sized
import Data.CFTA.Symbol (Symbol (RefinedSymbol), eraseRefinements)
import qualified Data.CFTA.Term as Term

-- | The two source states. Unknown state labels fail during decoding.
data State = Atom | Expr
    deriving (Eq, Ord, Show, Generic)

instance FromJSON State
instance ToJSON State

-- | Production identities are declared once and reused by updates.
pairName, twoName :: Language.ProductionName
pairName = "pair"
twoName = "two"

-- | References retain the state and production identity together.
pairRef, twoRef :: Language.ProductionRef State
pairRef = Language.at Expr pairName
twoRef = Language.at Atom twoName

-- | The source facts that this example removes explicitly.
positive, disabled :: Language.FactName
positive = "positive"
disabled = "disabled"

-- | The reversible exclusion stored with the language.
zeroPairRule :: Language.ExclusionName
zeroPairRule = "zero-pair"

-- | A symbol whose value is the given integer.
atom :: Symbol -> Integer -> Symbol
atom symbol value = RefinedSymbol symbol $ refinementFormula (.== fromInteger value)

-- | Keep named facts and recursive productions available for later updates.
original :: Language.Language State
original =
    Language.fromDocument
        $ either (error . Document.explainDocumentError) id
        $ Document.mkDocument
            Expr
            [
                ( Expr
                ,
                    [ FTA.Transition "pair" [Atom, Atom]
                        $ Document.Annotation (Language.productionNameText pairName)
                        $ Map.fromList
                            [ ("same", equalityConstraint $ mkEqConstraints [[path [0], path [1]]])
                            , (Language.factNameText positive, semanticConstraint $ Satisfies (path [0]) $ refinementFormula (.> 0))
                            , (Language.factNameText disabled, semanticConstraint Bottom)
                            ]
                    , FTA.Transition "wrap" [Expr] $ Document.Annotation "wrap" Map.empty
                    ]
                )
            ,
                ( Atom
                ,
                    [ FTA.Transition (atom "zero" 0) [] $ Document.Annotation "zero" Map.empty
                    , FTA.Transition (atom "one" 1) [] $ Document.Annotation "one" Map.empty
                    ]
                )
            ]

-- | Retain full refined symbols when selecting a term.
zeroPair :: Term.Term Symbol
zeroPair = Term.Node "pair" $ replicate 2 $ Term.Node (atom "zero" 0) []

-- | Compose constructor, constraint, and whole-term changes in one expression.
changes :: Language.Update State
changes =
    Language.define twoRef (atom "two" 2) []
        <> Language.relax pairRef disabled
        <> Language.relax pairRef positive
        <> Language.without zeroPairRule (Language.wholeTerm zeroPair)

-- | Apply an expression and report a selected source or exclusion error.
change :: Language.Language State -> Language.Update State -> IO (Language.Language State)
change before = either (fail . Language.explainUpdateError) pure . Language.update before

-- | Query the compiled constrained language at sizes three and four.
inspect :: Language.Language State -> IO ()
inspect language = withZ3 [] $ \solver -> do
    print $ map Language.exclusionNameText $ Map.keys $ Language.exclusions language
    classes <- Sized.sizedUpTo solver 4 (Language.compileGraph language) >>= either (fail . show) pure
    print $ map (Sized.countOfSize classes) [3, 4]
    mapM_ (print . map eraseRefinements . Sized.termsOfSize classes) [3, 4]

-- | Save the retained source and expressions with atomic file replacement.
save :: FilePath -> Language.Language State -> IO ()
save = saveWith encodeLanguage

-- | Save the readable form through the same atomic file operation.
saveText :: FilePath -> Language.Language State -> IO ()
saveText = saveWith $ ByteString.fromStrict . Text.encodeUtf8 . LanguageText.printLanguage

-- | Replace one file with the complete result of a chosen encoder.
saveWith :: (Language.Language State -> ByteString.ByteString) -> FilePath -> Language.Language State -> IO ()
saveWith encode target language =
    bracketOnError
        (openBinaryTempFile (takeDirectory target) ".cfta-language")
        (\(temporary, handle) -> hClose handle `finally` removeFile temporary)
        ( \(temporary, handle) -> do
            ByteString.hPut handle $ encode language
            hClose handle
            renameFile temporary target
        )

-- | Reopen the source and expressions without compiling or invoking a solver.
load :: FilePath -> IO (Language.Language State)
load filename = ByteString.readFile filename >>= either (fail . explainDecodeError) pure . decodeLanguage

-- | Read a complete text definition with the same typed source validation.
loadText :: FilePath -> IO (Language.Language State)
loadText filename = do
    bytes <- ByteString.readFile filename
    text <- either (fail . show) pure $ Text.decodeUtf8' $ ByteString.toStrict bytes
    either (fail . LanguageText.explainTextError) pure $ LanguageText.parseLanguage text

-- | Run the in-memory example or save, query, and restore in separate processes.
main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        [] -> do
            modified <- change original changes
            inspect modified
            change modified (Language.without zeroPairRule $ Language.subterm zeroPair) >>= inspect
            change modified (Language.restore zeroPairRule) >>= inspect
        ["print"] -> change original changes >>= ByteString.putStr . ByteString.fromStrict . Text.encodeUtf8 . LanguageText.printLanguage
        ["save-text", target] -> change original changes >>= saveText target
        ["show-text", filename] -> loadText filename >>= inspect
        ["restore-text", filename, target] -> do
            before <- loadText filename
            change before (Language.restore zeroPairRule) >>= saveText target
        ["save", target] -> change original changes >>= save target
        ["show", filename] -> load filename >>= inspect
        ["restore", filename, target] -> do
            before <- load filename
            change before (Language.restore zeroPairRule) >>= save target
        _ -> fail "usage: cfta-language-expressions [print | save[-text] FILE | show[-text] FILE | restore[-text] INPUT OUTPUT]"
