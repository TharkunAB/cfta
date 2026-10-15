{-# LANGUAGE OverloadedStrings #-}

{- | Tests of "Data.CFTA.Lean" against the oracle of @oracle/@: each mode
fills one goal. The oracle needs its Lake build and Lean's toolchain; without
them (as in a build without Lean), each test is pending with the reason.
-}
module Main (main) where

import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.Maybe (fromMaybe)
import System.Directory (doesDirectoryExist)
import System.Environment (lookupEnv)
import Test.Hspec (describe, hspec, it, pendingWith, shouldSatisfy)

import Data.CFTA.Gen.Synthesis (renderProgram)
import Data.CFTA.Gen.Synthesis.Walk (Fit (..))
import Data.CFTA.Lean

main :: IO ()
main = do
    directory <- oracleDirectory
    missing <- missingOracle directory
    let withOracleOr test = maybe test pendingWith missing
    hspec $ describe "Data.CFTA.Lean" $ do
        it "fills a goal in mode (a)" . withOracleOr $
            fits directory [(Hectare, Nothing)] >>= (`shouldSatisfy` elem "List.count x xs")
        it "fills a goal in mode (b)" . withOracleOr $
            fits directory [(States, Nothing)] >>= (`shouldSatisfy` elem "List.count x xs")

-- | The oracle's Lake project: @oracle@ in the package's directory, where cabal runs the tests.
oracleDirectory :: IO FilePath
oracleDirectory = do
    here <- doesDirectoryExist "oracle"
    fromMaybe (if here then "oracle" else "cfta-lean/oracle") <$> lookupEnv "CFTA_LEAN_ORACLE"

-- | The fits of up to three leaves of a goal over a small library, with the modes.
fits :: FilePath -> [(Mode, Maybe Double)] -> IO [String]
fits directory modes = withOracle directory [] $ \oracle -> do
    (components, _) <- library oracle ["List.count", "List.length", "List.reverse", "BEq.beq"]
    goal <- enterGoal oracle "∀ {α : Type} [BEq α] (x : α) (xs : List α), Nat"
    found <- newIORef []
    _ <- streamFits oracle defaultOptions{optionMaximumSize = 3, optionModes = modes} components goal $ \fit ->
        True <$ modifyIORef' found (renderProgram (fitProgram fit) :)
    readIORef found
