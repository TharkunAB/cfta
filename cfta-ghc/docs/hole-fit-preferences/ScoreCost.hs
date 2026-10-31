{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Measure shared corpus and preference scorers on varied program trees.
module Main (main) where

import Control.Monad (when, (>=>))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import System.Environment (getArgs)
import System.Exit (die)
import Text.Read (readMaybe)

import qualified Data.CFTA.GHC.Model as Corpus
import qualified Data.CFTA.GHC.Preference as Preference
import Data.CFTA.Gen.Synthesis (Program (..))
import Data.CFTA.Term (Term (..))

-- | One token scorer retained across all program scores.
type TokenScorer = Maybe (Text, Int) -> Int -> (Text, Int) -> Double

-- | Select a scorer, count, and optional serialized preference file.
main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        ["train"] -> require trained >>= Text.putStr . Preference.printPreferenceModel
        [mode] | validMode mode -> run mode 100000 Nothing
        [mode, countText]
            | validMode mode, Just count <- readMaybe countText, count > 0 -> run mode count Nothing
        [mode, countText, path]
            | validMode mode, Just count <- readMaybe countText, count > 0 -> run mode count (Just path)
        _ -> die "Usage: cfta-preference-score-cost train | (plain|empty|trained) [COUNT [PREFERENCE_FILE]]"

-- | Accept only the three scoring phases.
validMode :: String -> Bool
validMode mode = mode `elem` ["plain", "empty", "trained"]

-- | Turn a failed fixture or file load into an explicit process failure.
require :: Either String value -> IO value
require = either die pure

-- | Build real unigram and parent-position counts from a small term corpus.
base :: Corpus.FitModel
base = Corpus.fromTerms ["Prelude", "Data.List"] candidates examples
  where
    candidates = Map.fromList [("id", 1), ("reverse", 1), ("map", 2), ("abs", 1), ("drop", 2), ("take", 2), ("++", 2)]
    argument = Node "arg/0" []
    examples =
        replicate 40 ("top", Node "reverse/1" [argument])
            <> replicate 20 ("top", Node "map/2" [Node "abs/0" [], argument])
            <> replicate 10 ("top", Node "drop/2" [argument, argument])
            <> replicate 5 ("top", Node "var/1" [argument])
            <> [("expr", Node "++/2" [argument, Node "reverse/1" [argument]])]

-- | Module-use counts exercise shares for names classified as var.
uses :: Map.Map Text Int
uses = Map.fromList [("clean", 13), ("trim", 5), ("fresh", 2)]

-- | Local names classify as arg in all benchmark programs.
locals :: Set.Set Text
locals = Set.fromList ["xs", "ys", "n"]

-- | The hole's root scoring context.
root :: (Text, Int)
root = ("top", 0)

-- | Small pools of list expressions. The caller supplies their type discipline.
cases :: [Preference.PreferenceCase]
cases =
    [ Preference.PreferenceCase
        ("fixture-" <> Text.pack (show index))
        root
        locals
        uses
        (programAt (index * 8 + 4))
        [programAt (index * 8 + offset) | offset <- [0 .. 7]]
    | index <- [0 .. 2]
    ]

-- | Fit once when requested. The train command isolates this setup cost.
trained :: Either String Preference.PreferenceModel
trained = fst <$> Preference.trainPreferences 1000 0.01 base cases

-- | Score all modes through the same program traversal and strict checksum.
run :: String -> Int -> Maybe FilePath -> IO ()
run mode count path = do
    loaded <- traverse (Text.readFile >=> require . Preference.parsePreferenceModel) path
    let corpus = maybe base Preference.preferenceBase loaded
        original = Corpus.tokenScoreShared corpus uses root locals
        empty = Preference.tokenScoreShared (Preference.fromFitModel corpus) uses root locals
    scorer <- case mode of
        "plain" -> pure original
        "empty" -> pure empty
        _ -> do
            model <- maybe (require trained) pure loaded
            pure $ Preference.tokenScoreShared model uses root locals
    let (!tokens, !total) = foldl' (scoreAt scorer) (0, 0) [1 .. count]
    when (isNaN total || isInfinite total) $ die "A score was non-finite."
    print (count, tokens, total)
  where
    scoreAt scorer (!tokens, !total) index =
        let (!size, !value) = scoreProgramWith scorer $ programAt index
         in (tokens + size, total + fromIntegral index * value)

{- | Build fresh nested ASTs and specialization names from each runtime index.
The expressions have type [Int] when xs/ys :: [Int], n :: Int, and the
module names clean/trim :: [Int] -> [Int]. This driver does not invoke GHC.
-}
{-# NOINLINE programAt #-}
programAt :: Int -> Program
programAt index = case index `mod` 8 of
    0 -> xs
    1 -> App (named "reverse") xs
    2 -> mapped xs
    3 -> dropped $ App (named "reverse") xs
    4 -> App (named "clean") xs
    5 -> App (named "trim") $ mapped xs
    6 -> App (App (named "++") xs) $ App (named "reverse") (Var "ys")
    _ -> App (App (named "take") (Var "n")) $ App (named "clean") $ dropped xs
  where
    named name = Var $ name <> " " <> Text.pack (show index)
    xs = Var $ if even index then "xs" else "ys"
    mapped = App (App (named "map") (named "abs"))
    dropped = App (App (named "drop") (Var "n"))

-- | Use the plugin's application-spine traversal for every scoring mode.
{-# NOINLINE scoreProgramWith #-}
scoreProgramWith :: TokenScorer -> Program -> (Int, Double)
scoreProgramWith at = go Nothing 0
  where
    go parent position program =
        let (name, arguments) = spine program []
            token = (name, length arguments)
            !own = at parent position token
         in foldl' add (1, own) [go (Just token) index child | (index, child) <- zip [0 ..] arguments]
    add (!leftCount, !leftScore) (!rightCount, !rightScore) = (leftCount + rightCount, leftScore + rightScore)
    spine (Var name) arguments = (name, arguments)
    spine (App function argument) arguments = spine function (argument : arguments)
