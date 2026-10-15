{-# LANGUAGE OverloadedStrings #-}

{- | Hectare as the proposer of a Lean tactic: the mode (a) part of the
portfolio of @hectare?@ ("Oracle.Suggest" on the Lean side).

The tactic runs this program with pipes on its standard input and output, and
it is then the program's checker. The tactic writes the erased library (the
lines of the oracle's @library@ reply, up to @end@) and the goal (the lines
of the @goal@ reply, up to @end@). The program walks Hectare's programs as
"Data.CFTA.Lean" does: it writes @extend@ requests, and the tactic answers
them. At the end it writes @end outOfTime@ or @end exhausted@: whether it
stopped at its deadline or listed every program up to the size.

> hectare-propose SIZE SECONDS [ARGUMENT-ONLY...]
-}
module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import GHC.Clock (getMonotonicTimeNSec)
import System.Environment (getArgs)
import System.IO (BufferMode (LineBuffering), hFlush, hSetBuffering, hSetEncoding, stdin, stdout, utf8)

import Data.CFTA.Gen.Synthesis.Walk (Progress (..))
import Data.CFTA.Lean

main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        size : seconds : argumentOnly -> do
            mapM_ (`hSetEncoding` utf8) [stdin, stdout]
            hSetBuffering stdout LineBuffering
            let oracle = handleOracle stdout stdin
            (components, _) <- receiveLibrary oracle
            goal <- receiveGoal oracle
            start <- getMonotonicTimeNSec
            let options =
                    defaultOptions
                        { optionMaximumSize = read size
                        , optionArgumentOnly = map Text.pack argumentOnly
                        , optionDeadline = Just (start + round (read seconds * 1e9 :: Double))
                        }
            statistics <- streamFits oracle options components goal (const (pure True))
            Text.putStrLn ("end\t" <> if progressOutOfTime (statisticsProgress statistics) then "outOfTime" else "exhausted")
            hFlush stdout
        _ -> fail "usage: hectare-propose SIZE SECONDS [ARGUMENT-ONLY...]"
