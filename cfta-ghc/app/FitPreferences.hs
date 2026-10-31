{-# LANGUAGE OverloadedStrings #-}

-- | Train or evaluate conditional preferences over fixed candidate pools.
module Main (main) where

import Control.Monad (forM_, unless, when)
import Data.List (sortOn)
import qualified Data.Map.Strict as Map
import Data.Ord (Down (..))
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import System.Environment (getArgs)
import System.Exit (die)
import Text.Printf (printf)

import qualified Data.CFTA.GHC.Model as Corpus
import Data.CFTA.GHC.Preference
import Data.CFTA.Gen.Synthesis (Program)
import qualified Data.CFTA.Sized.Prefix.Train as Train

-- | Train one preference file or compare ranks on disjoint source groups.
main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        ["train", basePath, casesPath, output] -> do
            base <- Text.readFile basePath >>= either die pure . Corpus.parseFitModel
            cases <- readCases casesPath
            (model, report) <- either die pure $ trainPreferences 1000 0.01 base cases
            Text.writeFile output $ printPreferenceModel model
            printf
                "cases=%d corrections=%d steps=%d stop=%s gradient=%.9g\n"
                (length cases)
                (Map.size $ preferenceWeights model)
                (Train.fitStepCount report)
                (show $ Train.fitStopReason report)
                (Train.stepGradientNorm $ Train.fitFinalStep report)
        ["evaluate", modelPath, evaluationPath] -> do
            model <- Text.readFile modelPath >>= either die pure . parsePreferenceModel
            evaluation <- readCases evaluationPath
            when (Set.null $ preferenceGroups model) $
                die "The file has no recorded training groups. Use a trained preference file."
            let overlap = Set.intersection (preferenceGroups model) (groups evaluation)
            unless (Set.null overlap) $ die $ "Training and evaluation groups overlap: " <> show (Set.toAscList overlap)
            when (null evaluation) $ die "Supply at least one evaluation case."
            putStrLn "group,baseline_rank,preference_rank"
            forM_ evaluation $ \item -> do
                before <- either die pure $ rankPreferred (fromFitModel $ preferenceBase model) item
                after <- either die pure $ rankPreferred model item
                printf "%s,%d,%d\n" (Text.unpack $ csv $ caseGroup item) before after
        ["--help"] -> putStrLn usage
        _ -> die usage

-- | Keep the command surface limited to training and a group-disjoint comparison.
usage :: String
usage = "Usage: cfta-fit-preferences train BASE.cfta TRAIN.cases OUT.cfta | evaluate OUT.cfta TEST.cases"

-- | Read complete pools. Invalid records stop the operation.
readCases :: FilePath -> IO [PreferenceCase]
readCases path = Text.readFile path >>= either (die . ((path <> ": ") <>)) pure . parsePreferenceCases

-- | Source groups used to detect overlap between training and evaluation.
groups :: [PreferenceCase] -> Set.Set Text
groups = Set.fromList . map caseGroup

-- | Quote a CSV field without treating names as Haskell string literals.
csv :: Text -> Text
csv value = "\"" <> Text.replace "\"" "\"\"" value <> "\""

-- | Rank the preferred program. Equal scores keep the supplied candidate order.
rankPreferred :: PreferenceModel -> PreferenceCase -> Either String Int
rankPreferred model item = do
    let candidates = unique Set.empty (caseCandidates item)
        score = scoreProgram model item
        scored = [(program, score program) | program <- candidates]
    unless (all (\(_, value) -> not (isNaN value || isInfinite value)) scored) $
        Left "A candidate has a non-finite score."
    findRank 1 (casePreferred item) $ map fst $ sortOn (Down . snd) scored
  where
    findRank :: Int -> Program -> [Program] -> Either String Int
    findRank _ _ [] = Left $ Text.unpack (caseGroup item) <> ": preferred program absent from the supplied pool."
    findRank rank wanted (program : rest)
        | wanted == program = Right rank
        | otherwise = findRank (rank + 1) wanted rest
    unique _ [] = []
    unique seen (program : rest)
        | Set.member program seen = unique seen rest
        | otherwise = program : unique (Set.insert program seen) rest
