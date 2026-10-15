{-# LANGUAGE OverloadedStrings #-}

{- | List the programs of a Haskell type signature over the exports of some
modules, each checked in GHC's typechecker ("Data.CFTA.GHC.Fits"): a
synthesizer with GHC as the oracle.

> ghc-fits [-m MODULE[=QUALIFIER]]... [-p PACKAGE]... [--size N] [--fits N] [--seconds S] [--first-order | --only-defaulted] [--type-domains] [--rank] [--rank-pool N] [--model NAME] SIGNATURE

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
seconds, Hectare's rule 'hectareAvoid' applies, and Hectare's types are
curried ('optionCurried'). @--first-order@ searches with Hectare's
first-order types, and @--only-defaulted@ gives a variable that a program
does not determine only its default ('optionOnlyDefaulted'). @--type-domains@
gives a type variable of kind @Type@ the domain of its classes
('optionTypeDomains'). The figures of the search go to the standard
error.

With @--rank@, a decision model orders the programs ("Data.CFTA.GHC.Rank"):
ghc-fits finds @--rank-pool@ programs (50 by default) that use every part,
the model orders them, and ghc-fits prints the best @--fits@ of them. The
model runs on a local Ollama with the capability "decision": by default the
model of 'Decision.Ollama.defaultOllama' (Nimble v3, an external model
under its own license), or another with @--model@. The server loads the
model for the question (about 4 s). @--rank-pool@ and @--model@ also turn
the ranking on. When the model does not answer, the order stays.
-}
module Main (main) where

import Control.Monad.IO.Class (liftIO)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.Maybe (fromMaybe, isNothing)
import qualified Data.Set as Set
import qualified Data.Text as Text
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Text.Printf (printf)
import Text.Read (readMaybe)

import Data.CFTA.GHC.Fits
import Data.CFTA.GHC.Internal.Check (Counters (..))
import Data.CFTA.GHC.Rank (Ranking (..), defaultRanking, holeState, rankedFits)
import Data.CFTA.GHC.Session
import Data.CFTA.Gen.Synthesis (renderProgram)
import Decision.Ollama (Ollama (..), ollama)
import GHC.Core.Multiplicity (scaledThing)
import GHC.Tc.Utils.TcType (tcSplitFunTys, tcSplitNestedSigmaTys)
import GHC.Utils.Outputable (showPprUnsafe)

-- | The command line: the imports, the packages, the options, and the signature.
data Command = Command
    { commandImports :: [Import]
    , commandPackages :: [String]
    , commandOptions :: Options
    , commandRanking :: Maybe Ranking
    , commandSignature :: Maybe String
    }

-- | Read the command line; 'Left' gives the problem.
readCommand :: [String] -> Either String Command
readCommand = go (Command [] [] defaultOptions{optionAvoid = hectareAvoid, optionSeconds = Just 10} Nothing Nothing)
  where
    go command arguments = case arguments of
        [] -> Right command
        "-m" : module' : rest -> go command{commandImports = commandImports command <> [importOf module']} rest
        "-p" : package : rest -> go command{commandPackages = commandPackages command <> [package]} rest
        "--size" : value : rest -> number value >>= \size -> go (set command (\options -> options{optionMaximumSize = size})) rest
        "--fits" : value : rest -> number value >>= \fits -> go (set command (\options -> options{optionFits = fits})) rest
        "--seconds" : value : rest -> number value >>= \seconds -> go (set command (\options -> options{optionSeconds = Just seconds})) rest
        "--first-order" : rest -> go (set command (\options -> options{optionCurried = False})) rest
        "--only-defaulted" : rest -> go (set command (\options -> options{optionCurried = True, optionOnlyDefaulted = True})) rest
        "--type-domains" : rest -> go (set command (\options -> options{optionCurried = True, optionTypeDomains = True})) rest
        "--rank" : rest -> go (rank command id) rest
        "--rank-pool" : value : rest -> number value >>= \pool -> go (rank command (\r -> r{rankingPool = pool})) rest
        "--model" : model : rest -> go (rank command (\r -> r{rankingServer = (rankingServer r){ollamaModel = Text.pack model}})) rest
        signature : rest
            | isNothing (commandSignature command) && take 1 signature /= "-" -> go command{commandSignature = Just signature} rest
        other : _ -> Left ("unknown argument " <> other)
    set command change = command{commandOptions = change (commandOptions command)}
    rank command change = command{commandRanking = Just (change (fromMaybe defaultRanking (commandRanking command)))}
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
        Right (Command imports' packages options ranking (Just signature)) -> do
            let imports = if null imports' then [Import "Prelude" Nothing] else imports'
            withSessionOptions defaultSessionOptions{sessionPackages = packages} (map importLine imports) $ \session -> do
                candidates <- candidatesOf session imports
                typed <- typeOfExpression session ("undefined :: " <> signature)
                case typed of
                    Nothing -> hPutStrLn stderr ("GHC does not accept the signature " <> signature) >> exitFailure
                    Just typ -> do
                        let (_, _, rho) = tcSplitNestedSigmaTys typ
                            (parameters, result) = tcSplitFunTys rho
                            used = Set.fromList (map candidateName candidates)
                            names =
                                take
                                    (length parameters)
                                    [name | index <- [1 :: Int ..], let name = "x" <> Text.pack (show index), name `Set.notMember` used]
                            -- With a ranking, the model orders more programs than ghc-fits prints.
                            wanted = maybe (optionFits options) (max (optionFits options) . rankingPool) ranking
                        found <- newIORef []
                        let accept fit = liftIO $ do
                                modifyIORef' found (fit :)
                                fits <- readIORef found
                                pure (length (filter (not . fitIgnoresPart) fits) < wanted)
                        statistics <- fitsForSignature session options candidates typ names accept
                        fits <- reverse <$> readIORef found
                        ordered <- case ranking of
                            Just (Ranking pool server) -> do
                                model <- ollama server
                                let state =
                                        holeState
                                            (Just ("f", Text.pack signature, names))
                                            (Text.pack (showPprUnsafe result))
                                            [(name, Text.pack (showPprUnsafe (scaledThing parameter))) | (name, parameter) <- zip names parameters]
                                fst <$> rankedFits model state pool (Text.pack . renderProgram . fitProgram) fits
                            Nothing -> pure (filter (not . fitIgnoresPart) fits <> filter fitIgnoresPart fits)
                        let ranked = take (optionFits options) ordered
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
            "usage: ghc-fits [-m MODULE[=QUALIFIER]]... [-p PACKAGE]... [--size N] [--fits N] [--seconds S] [--first-order | --only-defaulted] [--type-domains] [--rank] [--rank-pool N] [--model NAME] SIGNATURE"
        exitFailure
