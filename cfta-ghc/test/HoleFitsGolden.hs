{- | The hole-fit plugin end to end: compile a module with typed holes, with
"Data.CFTA.GHC.HoleFits" as a static plugin, and compare GHC's messages
with a golden file. The messages have ASCII quotes and no colour, and the
plugin has a budget of programs and a time budget that it does not reach,
so that the output does not depend on the machine. With the variable
@GOLDEN_ACCEPT@ set, the test writes the golden file.
-}
module Main (main) where

import Control.Monad (unless, void, when)
import Control.Monad.IO.Class (liftIO)
import Data.Char (isSpace)
import Data.Maybe (isJust)
import System.Directory (doesFileExist, getTemporaryDirectory, removeFile)
import System.Environment (lookupEnv)
import System.Exit (exitFailure)
import System.IO (hClose, openTempFile)
import System.Process (readProcess)

import Data.CFTA.GHC.HoleFits (plugin)
import GHC (LoadHowMuch (LoadAllTargets), getSessionDynFlags, guessTarget, load, runGhc, setSessionDynFlags, setTargets)
import GHC.Data.Bool (OverridingBool (Never))
import GHC.Driver.Backend (noBackend)
import GHC.Driver.DynFlags (DynFlags (backend, ghcLink, useColor, useUnicode), GhcLink (NoLink))
import GHC.Driver.Env (HscEnv (hsc_plugins))
import GHC.Driver.Monad (modifySession, pushLogHookM)
import GHC.Driver.Plugins (PluginWithArgs (..), Plugins (staticPlugins), StaticPlugin (..))
import GHC.Runtime.Loader (initializeSessionPlugins)
import GHC.Utils.Logger (defaultLogActionWithHandles)

-- | The module with the holes, and the golden file of GHC's messages.
source, golden :: FilePath
source = "test/holes/Holes.hs"
golden = "test/holes/Holes.golden"

-- | The plugin's options: at most four leaves and five fits for each hole.
options :: [String]
options = ["size=4", "fits=5", "programs=1000000", "seconds=1000"]

main :: IO ()
main = do
    libdir <- maybe (trim <$> readProcess "ghc" ["--print-libdir"] "") pure =<< lookupEnv "GHC_LIBDIR"
    temporary <- getTemporaryDirectory
    (logPath, logHandle) <- openTempFile temporary "holes.log"
    runGhc (Just libdir) $ do
        flags <- getSessionDynFlags
        void $ setSessionDynFlags flags{backend = noBackend, ghcLink = NoLink, useUnicode = False, useColor = Never}
        modifySession $ \environment ->
            environment
                { hsc_plugins = (hsc_plugins environment){staticPlugins = [StaticPlugin (PluginWithArgs plugin options) False]}
                }
        -- As the ghc program does: run the driver plugins before GHC reads
        -- the modules, so that the modules get the flags that the plugins set.
        initializeSessionPlugins
        pushLogHookM (const (defaultLogActionWithHandles logHandle logHandle))
        target <- guessTarget source Nothing Nothing
        setTargets [target]
        void (load LoadAllTargets)
        liftIO (hClose logHandle)
    output <- readFile logPath
    length output `seq` removeFile logPath
    accept <- isJust <$> lookupEnv "GOLDEN_ACCEPT"
    when accept $ writeFile golden output
    exists <- doesFileExist golden
    unless exists $ do
        putStrLn ("No golden file " <> golden <> "; set GOLDEN_ACCEPT to write it.")
        exitFailure
    expected <- readFile golden
    unless (output == expected) $ do
        putStrLn ("The messages differ from " <> golden <> ":")
        putStr output
        exitFailure
    putStrLn ("The messages are as in " <> golden <> ".")
  where
    trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace
