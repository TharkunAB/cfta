{-# LANGUAGE OverloadedStrings #-}

{- | List the programs of a Haskell type signature over the exports of some
modules, each checked in GHC's typechecker ("Data.CFTA.GHC.Fits"): a
synthesizer with GHC as the oracle.

> ghc-fits [-m MODULE[=QUALIFIER]]... [-p PACKAGE]... [--size N] [--fits N] [--seconds S] SIGNATURE

For example:

> ghc-fits -m Prelude -m Data.Maybe '(a -> Bool) -> [a] -> Int'
> ghc-fits -m Data.Map=Map --size 4 'Ord k => k -> v -> Map.Map k v -> Map.Map k v'

The signature can have a class context; it becomes the givens of the
search. Each argument of the signature is a variable that a program uses
once, and the programs print as lambdas, one on each line, smallest first.
The programs that ignore part of themselves ('fitIgnoresPart') come after
the others. The modules are Prelude when no @-m@ is given; @=QUALIFIER@
imports a module qualified; @-p@ exposes a package. By default, the
programs have up to five leaves, the search stops after ten fits or ten
seconds, and Hectare's rule 'hectareAvoid' applies. The figures of the
search go to the standard error.
-}
module Main (main) where

import Control.Monad.IO.Class (liftIO)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.Maybe (isNothing)
import qualified Data.Set as Set
import qualified Data.Text as Text
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Text.Printf (printf)
import Text.Read (readMaybe)

import Data.CFTA.GHC.Fits
import Data.CFTA.GHC.Internal.Check (Counters (..))
import Data.CFTA.GHC.Session
import Data.CFTA.Gen.Synthesis (renderProgram)
import GHC.Tc.Utils.TcType (tcSplitFunTys, tcSplitNestedSigmaTys)

-- | The command line: the imports, the packages, the options, and the signature.
data Command = Command
    { commandImports :: [Import]
    , commandPackages :: [String]
    , commandOptions :: Options
    , commandSignature :: Maybe String
    }

-- | Read the command line; 'Left' gives the problem.
readCommand :: [String] -> Either String Command
readCommand = go (Command [] [] defaultOptions{optionAvoid = hectareAvoid, optionSeconds = Just 10} Nothing)
  where
    go command arguments = case arguments of
        [] -> Right command
        "-m" : module' : rest -> go command{commandImports = commandImports command <> [importOf module']} rest
        "-p" : package : rest -> go command{commandPackages = commandPackages command <> [package]} rest
        "--size" : value : rest -> number value >>= \size -> go (set command (\options -> options{optionMaximumSize = size})) rest
        "--fits" : value : rest -> number value >>= \fits -> go (set command (\options -> options{optionFits = fits})) rest
        "--seconds" : value : rest -> number value >>= \seconds -> go (set command (\options -> options{optionSeconds = Just seconds})) rest
        signature : rest
            | isNothing (commandSignature command) && take 1 signature /= "-" -> go command{commandSignature = Just signature} rest
        other : _ -> Left ("unknown argument " <> other)
    set command change = command{commandOptions = change (commandOptions command)}
    importOf text = case break (== '=') text of
        (name, '=' : qualifier) -> Import name (Just qualifier)
        (name, _) -> Import name Nothing
    number :: (Read a) => String -> Either String a
    number value = maybe (Left ("not a number: " <> value)) Right (readMaybe value)

main :: IO ()
main = do
    arguments <- getArgs
    case readCommand arguments of
        Left problem -> usage problem
        Right Command{commandSignature = Nothing} -> usage "no signature"
        Right (Command imports' packages options (Just signature)) -> do
            let imports = if null imports' then [Import "Prelude" Nothing] else imports'
            withSessionOptions defaultSessionOptions{sessionPackages = packages} (map importLine imports) $ \session -> do
                candidates <- candidatesOf session imports
                typed <- typeOfExpression session ("undefined :: " <> signature)
                case typed of
                    Nothing -> hPutStrLn stderr ("GHC does not accept the signature " <> signature) >> exitFailure
                    Just typ -> do
                        let (_, _, rho) = tcSplitNestedSigmaTys typ
                            used = Set.fromList (map candidateName candidates)
                            names =
                                take
                                    (length (fst (tcSplitFunTys rho)))
                                    [name | index <- [1 :: Int ..], let name = "x" <> Text.pack (show index), name `Set.notMember` used]
                        found <- newIORef []
                        let accept fit = liftIO $ do
                                modifyIORef' found (fit :)
                                fits <- readIORef found
                                pure (length (filter (not . fitIgnoresPart) fits) < optionFits options)
                        statistics <- fitsForSignature session options candidates typ names accept
                        fits <- reverse <$> readIORef found
                        let ranked = take (optionFits options) (filter (not . fitIgnoresPart) fits <> filter fitIgnoresPart fits)
                            lambda = if null names then "" else "\\" <> unwords (map Text.unpack names) <> " -> "
                        mapM_ (\fit -> putStrLn (lambda <> renderProgram (fitProgram fit))) ranked
                        case statistics of
                            Just figures ->
                                hPutStrLn stderr $
                                    printf
                                        "%d programs, %d skipped, %d fits, %d solver calls, %d candidates%s"
                                        (statisticsPrograms figures)
                                        (statisticsSkipped figures)
                                        (statisticsFits figures)
                                        (countSolverCalls (statisticsCounters figures))
                                        (length candidates)
                                        (if statisticsOutOfTime figures then ", out of time" else "" :: String)
                            Nothing -> hPutStrLn stderr "the search failed" >> exitFailure
  where
    importLine (Import name Nothing) = "import " <> name
    importLine (Import name (Just qualifier)) = "import qualified " <> name <> " as " <> qualifier
    usage problem = do
        hPutStrLn stderr problem
        hPutStrLn
            stderr
            "usage: ghc-fits [-m MODULE[=QUALIFIER]]... [-p PACKAGE]... [--size N] [--fits N] [--seconds S] SIGNATURE"
        exitFailure
