{-# LANGUAGE OverloadedStrings #-}

-- | Compose language updates in memory, then save, reopen, and restore an exclusion.
module Main (main) where

import Control.Exception (bracketOnError, finally)
import qualified Data.ByteString.Lazy as ByteString
import qualified Data.Map.Strict as Map
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
import qualified Data.CFTA.Sized as Sized
import Data.CFTA.Symbol (Symbol (RefinedSymbol), eraseRefinements)
import qualified Data.CFTA.Term as Term

-- | A symbol whose value is the given integer.
atom :: Symbol -> Integer -> Symbol
atom symbol value = RefinedSymbol symbol $ refinementFormula (.== fromInteger value)

-- | Keep named facts and recursive productions available for later updates.
original :: Language.Language String
original =
    Language.fromDocument
        $ either (error . Document.explainDocumentError) id
        $ Document.mkDocument
            "Expr"
            [
                ( "Expr"
                ,
                    [ FTA.Transition "pair" ["Atom", "Atom"]
                        $ Document.Annotation "pair"
                        $ Map.fromList
                            [ ("same", equalityConstraint $ mkEqConstraints [[path [0], path [1]]])
                            , ("positive", semanticConstraint $ Satisfies (path [0]) $ refinementFormula (.> 0))
                            , ("disabled", semanticConstraint Bottom)
                            ]
                    , FTA.Transition "wrap" ["Expr"] $ Document.Annotation "wrap" Map.empty
                    ]
                )
            ,
                ( "Atom"
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
changes :: Language.Update String
changes =
    Language.define (Language.at "Atom" "two") (atom "two" 2) []
        <> Language.relax (Language.at "Expr" "pair") "disabled"
        <> Language.relax (Language.at "Expr" "pair") "positive"
        <> Language.without "zero-pair" (Language.wholeTerm zeroPair)

-- | Apply an expression and report a selected source or exclusion error.
change :: Language.Language String -> Language.Update String -> IO (Language.Language String)
change before = either (fail . Language.explainUpdateError) pure . Language.update before

-- | Query the compiled constrained language at sizes three and four.
inspect :: Language.Language String -> IO ()
inspect language = withZ3 [] $ \solver -> do
    print $ Map.keys $ Language.exclusions language
    classes <- Sized.sizedUpTo solver 4 (Language.compileGraph language) >>= either (fail . show) pure
    print $ map (Sized.countOfSize classes) [3, 4]
    mapM_ (print . map eraseRefinements . Sized.termsOfSize classes) [3, 4]

-- | Save the retained source and expressions with atomic file replacement.
save :: FilePath -> Language.Language String -> IO ()
save target language =
    bracketOnError
        (openBinaryTempFile (takeDirectory target) ".cfta-language.json")
        (\(temporary, handle) -> hClose handle `finally` removeFile temporary)
        ( \(temporary, handle) -> do
            ByteString.hPut handle $ encodeLanguage language
            hClose handle
            renameFile temporary target
        )

-- | Reopen the source and expressions without compiling or invoking a solver.
load :: FilePath -> IO (Language.Language String)
load filename = ByteString.readFile filename >>= either (fail . explainDecodeError) pure . decodeLanguage

-- | Run the in-memory example or save, query, and restore in separate processes.
main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        [] -> do
            modified <- change original changes
            inspect modified
            change modified (Language.without "zero-pair" $ Language.subterm zeroPair) >>= inspect
            change modified (Language.restore "zero-pair") >>= inspect
        ["save", target] -> change original changes >>= save target
        ["show", filename] -> load filename >>= inspect
        ["restore", filename, target] -> do
            before <- load filename
            change before (Language.restore "zero-pair") >>= save target
        _ -> fail "usage: cfta-language-expressions [save FILE | show FILE | restore INPUT OUTPUT]"
