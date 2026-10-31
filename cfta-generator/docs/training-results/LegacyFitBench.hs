-- | Compare the legacy training APIs in two separately compiled revisions.
module Main (main) where

import Control.Monad (forM_)
import qualified Data.Map.Strict as Map
import System.Environment (getArgs)
import System.Exit (die)
import Text.Read (readMaybe)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Sized.Prefix.Train
import Data.CFTA.Term (Term (..))

-- | A strict count and checksum force all numerical fields without trace output.
data Score = Score !Int !Double
    deriving (Show)

-- | Run exact textual comparison fixtures or a varied optimizer workload.
main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        ["trace"] -> traces
        ["bench"] -> benchmark 32
        ["bench", jobsText]
            | Just jobs <- readMaybe jobsText, jobs > 0 -> benchmark jobs
        _ -> die "Usage: legacy-fit trace | legacy-fit bench [POSITIVE_JOB_COUNT]"

-- | A recursive grammar from the existing training tests: x, y, neg(e), add(e,e).
expressions :: FTA.FTA String String Constraint
expressions =
    either (error . show) id $
        FTA.mkFTA "e" [("e", [node "x" [], node "y" [], node "neg" ["e"], node "add" ["e", "e"]])]
  where
    node symbol children = FTA.Transition symbol children noConstraint

-- | Vary the finite size bound while keeping all ordinary corpus shapes supported.
boundFor :: Int -> Int
boundFor job = 5 + job `mod` 4

-- | Use distinct finite teacher parameters for each job, with no repeated seed cycle.
teacherFor :: Int -> LogWeights String
teacherFor job =
    let fraction = fromIntegral job / fromIntegral (job + 37)
     in Map.fromList
            [ ("x", 0.4 + 0.2 * fraction)
            , ("y", -0.3 - 0.15 * fraction)
            , ("neg", -0.8 + 0.1 * fraction)
            , ("add", -1.2 - 0.2 * fraction)
            ]

-- | Get feasible target means from the same language at the teacher weights.
inputs :: Int -> (Oracle String, Map.Map String Double, LogWeights String, Double)
inputs job =
    let oracle = automatonOracle expressions $ boundFor job
        counts = snd $ oracleExpectations oracle $ teacherFor job
        start = Map.fromList [("x", -0.1), ("neg", 0.05 / fromIntegral (job + 1))]
        precision = if even job then 1e-3 else 0
     in (oracle, counts, start, precision)

-- | Exercise default distillation with duplicates, an oversized term, and a rejection.
corpusFor :: Int -> [Term String]
corpusFor job =
    replicate (7 + job `mod` 11) x
        ++ replicate (5 + job `mod` 7) y
        ++ replicate (3 + job `mod` 5) (Node "neg" [x])
        ++ [ Node "add" [x, y]
           , Node "add" [x, Node "neg" [y]]
           , Node "neg" [Node "add" [x, y]]
           , iterate (\term -> Node "neg" [term]) x !! (boundFor job + 2)
           , Node "outside" []
           ]
  where
    x = Node "x" []
    y = Node "y" []

-- | Print every field of bounded traces and exact Show values of default distill.
traces :: IO ()
traces = do
    forM_ [1 .. 6] $ \job -> do
        let (oracle, counts, start, precision) = inputs job
            steps = take 100 $ fit precision oracle counts start
        print ("input", job, boundFor job, precision, counts, start)
        forM_ [1, 2, 5, 100] $ \limit -> print ("fit", job, limit, take limit steps)
        print ("distill", job, distill expressions (boundFor job) (corpusFor job))
    let oracle = automatonOracle expressions 6
        uniform = snd $ oracleExpectations oracle Map.empty
        shifted =
            Oracle
                (oracleSymbols oracle)
                (\point -> 1e12 + oracleLogPartition oracle point)
                (\point -> let (value, counts) = oracleExpectations oracle point in (1e12 + value, counts))
        nearby = snd $ oracleExpectations oracle $ Map.singleton "x" 1e-3
    print ("stationary", take 100 $ fit 0 oracle uniform Map.empty)
    print ("small-objective-change", take 100 $ fit 0 shifted nearby Map.empty)
    -- This deliberately inconsistent oracle exercises the failed-search branch.
    let failedSearch = Oracle ["x"] (const 2) (const (0, Map.empty))
    print ("failed-search", take 100 $ fit 0 failedSearch (Map.singleton "x" 1) Map.empty)
    print ("distill-empty", distill expressions 6 [])
    print ("distill-rejected", distill expressions 6 [Node "outside" []])

-- | Include every fitted weight, in stable key order, in the strict checksum.
weightScore :: LogWeights String -> Double
weightScore weights =
    sum [fromIntegral index * weight | (index, (_, weight)) <- zip [1 :: Int ..] $ Map.toAscList weights]

-- | Force a whole bounded trace without retaining it or converting it to text.
scoreTrace :: [Step String] -> Score
scoreTrace = foldl' add (Score 0 0)
  where
    add (Score count total) step =
        Score (count + 1) (total + stepObjective step + 0.25 * stepGradientNorm step + weightScore (stepWeights step))

-- | Run two real legacy APIs with job-dependent inputs, outside any shared CAF.
runJob :: Int -> Score
runJob job =
    let (oracle, counts, start, precision) = inputs job
        Score steps checksum = scoreTrace $ take 100 $ fit precision oracle counts start
        distilled = case distill expressions (boundFor job) (corpusFor job) of
            Nothing -> error "The benchmark corpus unexpectedly had no supported distillation."
            Just weights -> weights
     in Score steps (checksum + weightScore distilled)
{-# NOINLINE runJob #-}

-- | Measure varied bounded fits and default distill; print only the forced result.
benchmark :: Int -> IO ()
benchmark jobs = do
    let Score steps checksum = foldl' add (Score 0 0) [1 .. jobs]
        add (Score count total) job = case runJob job of
            Score nextCount nextTotal -> Score (count + nextCount) (total + nextTotal)
    if isNaN checksum || isInfinite checksum
        then die "The legacy workload produced a non-finite checksum."
        else print (jobs, steps, checksum)
