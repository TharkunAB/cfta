{-# LANGUAGE OverloadedStrings #-}

{- | Build and merge fit models ("Data.CFTA.GHC.Model"), the models that order
the fits of the hole-fit plugin (option @model@ of "Data.CFTA.GHC.HoleFits").

> cfta-fit-model build FILES OUT [MODULE...]
> cfta-fit-model merge MODEL MODEL OUT

@build@ reads the paths of Haskell modules from FILES, one on each line. The
candidates are those that cfta-ghc reads from the Prelude, "Data.List",
"Data.Maybe", "Data.Either", "Data.Char", and the extra MODULEs. The program
parses each module ("Data.CFTA.GHC.Corpus"), keeps the terms of two nodes or
more, and writes the model of their counts to OUT in the text form
@fit-model 1;@. A module that does not parse, or uses CPP, is skipped.

@merge@ adds the counts of two models and writes the result to OUT.
-}
module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Text.Printf (printf)

import GHC.Core.Type (splitFunTys)
import GHC.Tc.Utils.TcType (tcSplitSigmaTy)

import Data.CFTA.GHC.Corpus (moduleTerms, newParser)
import Data.CFTA.GHC.Fits (Candidate (..))
import Data.CFTA.GHC.Model (FitModel, fromTerms, merge, parseFitModel, printFitModel)
import Data.CFTA.GHC.Session (Import (..), candidatesOf, withSession)

main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        "build" : files : out : extra -> build files out extra
        ["merge", left, right, out] -> do
            model <- merge <$> load left <*> load right
            Text.writeFile out (printFitModel model)
        _ -> do
            hPutStrLn stderr "usage: cfta-fit-model build FILES OUT [MODULE...] | cfta-fit-model merge MODEL MODEL OUT"
            exitFailure

-- | Build the model of the modules that a file lists.
build :: FilePath -> FilePath -> [String] -> IO ()
build files out extra = do
    paths <- lines <$> readFile files
    let modules = ["Prelude", "Data.List", "Data.Maybe", "Data.Either", "Data.Char"] <> extra
    withSession ["import " <> name | name <- modules] $ \session -> do
        candidates <- candidatesOf session [Import name Nothing | name <- modules]
        let arities = Map.fromList [(candidateName candidate, arity (candidateType candidate)) | candidate <- candidates]
        parser <- newParser session
        found <- mapM (moduleTerms parser (map Text.pack modules) (Map.keysSet arities)) paths
        let terms = [kept | kept@(_, term) <- concat (catMaybes found), length (foldr (:) [] term) >= 2]
        Text.writeFile out (printFitModel (fromTerms (map Text.pack modules) arities terms))
        printf
            "candidates %d, modules parsed %d of %d, terms %d\n"
            (Map.size arities)
            (length (catMaybes found))
            (length paths)
            (length terms)
  where
    arity typ = let (_, _, tau) = tcSplitSigmaTy typ in length (fst (splitFunTys tau))

-- | Read a model from a file, or stop with the error.
load :: FilePath -> IO FitModel
load path = do
    text <- Text.readFile path
    case parseFitModel text of
        Right model -> pure model
        Left message -> hPutStrLn stderr (path <> ": " <> message) >> exitFailure
