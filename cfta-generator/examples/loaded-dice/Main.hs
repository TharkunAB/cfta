-- | Tune an existing generator, compare direct class control, and replay samples.
module Main (main) where

import Control.Monad (forM, forM_, replicateM, unless)
import qualified Data.Map.Strict as Map
import Data.Maybe (isNothing)
import System.Environment (getArgs)
import System.Exit (die)
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import Text.Printf (printf)
import Text.Read (readMaybe)

import qualified Data.CFTA.Gen as G
import qualified Data.CFTA.Gen.QuickCheck as GQ
import Data.CFTA.Index (Rank (..))
import qualified Data.CFTA.Sized.Prefix as P
import Data.CFTA.Term (Term)

import ListGenerator

-- | Run the paper example, its focused checks, or a rank replay.
main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        [] -> demo
        ["demo"] -> demo
        ["check"] -> either die (const $ putStrLn "PASS: exact masses, requested classes, bounded samples, and rank replay.") checks
        ["replay", method, rankText]
            | Just rank <- readMaybe rankText -> either die print $ replay method $ Rank rank
        ["--help"] -> putStrLn usage
        _ -> die usage

-- | The command syntax. The default run uses 10,000 draws and seed 1729.
usage :: String
usage =
    "Usage: cfta-loaded-dice [demo|check|replay cfta RANK|replay direct RANK]\n  demo: tune the reference list generator and compare direct length control."

-- | Choose requested classes with Gen.frequency after checking each class exists.
directGenerator :: Map.Map Int Integer -> Either String (G.Gen String [Int])
directGenerator requested = do
    _ <- targetMasses requested
    alternatives <- forM (Map.toAscList requested) $ \(size, weight) -> do
        branch <- maybe (Left $ "Missing requested length class: " ++ show size) Right $ Map.lookup size classes
        count <- either (Left . show) Right $ G.cardinality branch
        unless (count > 0) $ Left $ "Empty requested length class: " ++ show size
        pure (fromInteger weight, branch)
    pure $ G.frequency alternatives
  where
    classes = Map.fromList [(size, replicateM size $ G.elements [0 .. alphabetSize - 1]) | size <- [0 .. maximumLength]]

-- | Attach local rational probabilities to the full CFTA language.
weighted :: Parameters -> Either String (P.Completions Choice)
weighted parameters = do
    full <- listEvent Nothing
    weights <- rationalWeights parameters
    maybe (Left "A symbol has a negative sampling weight.") Right $ P.withWeights weights full

-- | Draw a reproducible sequence with the current QuickCheck version.
draw :: Int -> QC.Gen value -> [value]
draw count generator = unGen (QC.vectorOf count generator) (mkQCGen 1729) 30

-- | Draw weighted integer ranks with one retained total and decoder.
drawTerms :: Int -> P.Completions Choice -> Either String [Term Choice]
drawTerms count completions = do
    let total = P.weightedTotal completions
        decodeRank = P.unrankWeighted completions
    unless (total > 0) $ Left "The generator has zero total sampling mass."
    traverse
        (\ticket -> maybe (Left "A weighted rank has no completion.") Right $ decodeRank ticket)
        (draw count $ QC.chooseInteger (0, total - 1))

-- | Count observed lengths, including repeated samples.
counts :: [[value]] -> Map.Map Int Int
counts lists = Map.fromListWith (+) [(length values, 1) | values <- lists]

-- | Print exact class masses, observed counts, and replay commands for actual lists.
demo :: IO ()
demo = either die display $ do
    (fitted, beforeKL, afterKL) <- fit
    before <- weighted initial
    after <- weighted fitted
    beforeTerms <- drawTerms 10000 before
    afterTerms <- drawTerms 10000 after
    beforeLists <- traverse decode beforeTerms
    afterLists <- traverse decode afterTerms
    beforeMasses <- rationalWeights initial >>= lengthMasses
    afterMasses <- rationalWeights fitted >>= lengthMasses
    target <- targetMasses requestedWeights
    direct <- directGenerator requestedWeights
    let directDraws = draw 10000 $ GQ.toGenWithRank direct
    replays <- forM (take 5 afterTerms) $ \term -> do
        rank <- maybe (Left "A generated term has no replay rank.") Right $ P.rankCompletion after term
        value <- decode term
        pure (rank, value)
    pure (beforeKL, afterKL, beforeMasses, afterMasses, target, counts beforeLists, counts afterLists, directDraws, replays)
  where
    display (beforeKL, afterKL, beforeMasses, afterMasses, target, beforeCounts, afterCounts, directDraws, replays) = do
        printf "KL(target || lengths): %.12f -> %.12f\n" beforeKL afterKL
        putStrLn "10000 lists per method; seed 1729. Probabilities below are rounded; counts are observed."
        putStrLn "length,target,initial_probability,trained_probability,initial_count,trained_count,direct_count"
        let directCounts = counts $ map G.rankedValue directDraws
        forM_ [0 .. maximumLength] $ \size ->
            printf
                "%d,%.9f,%.9f,%.9f,%d,%d,%d\n"
                size
                (fromRational (Map.findWithDefault 0 size target) :: Double)
                (fromRational (beforeMasses Map.! size) :: Double)
                (fromRational (afterMasses Map.! size) :: Double)
                (Map.findWithDefault 0 size beforeCounts)
                (Map.findWithDefault 0 size afterCounts)
                (Map.findWithDefault 0 size directCounts)
        putStrLn "Training tunes the existing stop/continue choices. Direct length control needs no training."
        forM_ replays $ \(Rank rank, value) -> printf "replay cfta %d => %s\n" rank (show value)
        forM_ (take 5 directDraws) $ \sample ->
            let Rank rank = G.valueRank sample
             in printf "replay direct %d => %s\n" rank (show $ G.rankedValue sample)

-- | Replay a rank in the selected language; weights do not change CFTA term ranks.
replay :: String -> Rank -> Either String [Int]
replay method rank = case method of
    "cfta" -> do
        full <- listEvent Nothing
        term <- maybe (Left "The CFTA rank is outside the bounded language.") Right $ P.unrankCompletion full rank
        decode term
    "direct" -> do
        direct <- directGenerator requestedWeights
        either (Left . show) Right $ G.unrank direct rank
    _ -> Left "Select the cfta or direct replay language. Their ranks are not interchangeable."

-- | Check exact probabilities and replay without the larger research test suite.
checks :: Either String ()
checks = do
    (fitted, _, finalKL) <- fit
    ensure "The reference KL changed." $ abs (finalKL - 0.010197463841708753) < 1e-11
    forM_ [initial, fitted] $ \parameters -> do
        full <- weighted parameters
        ensure "Rational list mass must be exactly one." $ P.completionWeight full == 1
        masses <- rationalWeights parameters >>= lengthMasses
        ensure "Rational length mass must be exactly one." $ sum masses == 1
        weights <- rationalWeights parameters
        let total = P.weightedTotal full
            interval = P.rankWeighted full
            decodeRank = P.unrankWeighted full
        ensure "Weighted ranks outside the ticket space must be rejected." $
            isNothing (decodeRank (-1)) && isNothing (decodeRank total)
        terms <- drawTerms 100 full
        forM_ terms $ \term -> do
            value <- decode term
            ensure "A sample violates the length or element bound." $ valid value
            (start, width) <- maybe (Left "A sample has no weighted interval.") Right $ interval term
            ensure "A weighted interval has an invalid boundary." $
                width > 0 && decodeRank start == Just term && decodeRank (start + width - 1) == Just term
            ensure "A weighted interval has the wrong probability." $
                fromInteger width / fromInteger total == product (map weights $ foldr (:) [] term)
            rank <- maybe (Left "A sample has no term rank.") Right $ P.rankCompletion full term
            restored <- replay "cfta" rank
            ensure "CFTA replay changed the list." $ restored == value
    direct <- directGenerator requestedWeights
    expected <- targetMasses requestedWeights
    actual <- either (Left . show) (Right . Map.fromList) $ G.pmf $ length <$> direct
    ensure "Direct class probabilities differ from the target." $ actual == expected
    forM_ (draw 100 $ GQ.toGenWithRank direct) $ \sample -> do
        restored <- replay "direct" $ G.valueRank sample
        ensure "Direct replay changed the list." $ restored == G.rankedValue sample && valid restored
    case directGenerator (Map.singleton (maximumLength + 1) 1) of
        Left _ -> pure ()
        Right _ -> Left "A missing requested class was silently discarded."
    case rationalWeights (Map.singleton 1 (0 / 0)) of
        Left _ -> pure ()
        Right _ -> Left "A non-finite logit reached rational conversion."
    full <- listEvent Nothing
    zero <- maybe (Left "Zero symbol weights must be accepted.") Right $ P.withWeights (const 0) full
    case drawTerms 1 zero of
        Left _ -> pure ()
        Right _ -> Left "A zero-mass language was sampled."
  where
    valid values = length values <= maximumLength && all (\value -> value >= 0 && value < alphabetSize) values

-- | Return a useful message when a recipe check fails.
ensure :: String -> Bool -> Either String ()
ensure message condition = unless condition $ Left message
