-- | Compare a structural token prefilter with a constrained CFTA cursor.
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (foldM, forM_, replicateM_, unless)
import Data.Either (isRight)
import Data.IORef (newIORef, readIORef)
import qualified Data.IntMap.Strict as IntMap
import Data.List (intercalate)
import Data.Word (Word64)
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import System.Exit (die)
import Text.Read (readMaybe)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (equalityConstraint, noConstraint)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Index (Size (..))
import Data.CFTA.Mask (Mask (..), completionsMask)
import Data.CFTA.Mask.Text (TextToken (..), textMask)
import Data.CFTA.Mask.Vocabulary (Vocabulary, vocabulary, vocabularyMask)
import Data.CFTA.Path (path)
import Data.CFTA.Sized.Prefix (prefixCompletions)
import Data.CFTA.Term (Term)

{- | The expression and atom states. An operator has an expression on the
left and an atom on the right. A pair of parentheses costs one AST node.
-}
startMask :: Bool -> Size -> Bool -> IO (Mask TextToken (Term Char))
startMask infixNotation bound equalChildren = do
    let atoms = [FTA.Transition c [] noConstraint | c <- "ab"] <> [FTA.Transition '(' ['E'] noConstraint]
        constraint '+' | equalChildren = equalityConstraint $ mkEqConstraints [[path [0], path [1]]]
        constraint _ = noConstraint
        operators = [FTA.Transition c ['E', 'A'] (constraint c) | c <- "+*"]
        texts '(' = ["(", ")"]
        texts c | c `elem` "+*" = if infixNotation then ["", [c], ""] else [[c], "", ""]
        texts c = [[c]]
    graph <- either (die . show) pure $ FTA.mkFTA 'E' [('E', atoms <> operators), ('A', atoms)]
    completions <- either (die . show) pure $ prefixCompletions bound graph
    pure $ textMask texts (completionsMask completions)

-- | Read the token IDs and their spelling. Empty spelling denotes EOS.
readVocabulary :: FilePath -> IO (IntMap.IntMap [TextToken])
readVocabulary file = do
    rows <- traverse row . lines =<< readFile file
    let entries = IntMap.fromList rows
    unless (length rows == IntMap.size entries) $ die "duplicate token ID"
    unless (length (filter (== [EndOfText]) (IntMap.elems entries)) == 1) $ die "expected one EOS"
    pure entries
  where
    row line = case break (== '\t') line of
        (field, '\t' : value)
            | Just i <- readMaybe field
            , i >= 0 ->
                pure (i, if null value then [EndOfText] else map Character value)
        _ -> die "expected token ID, tab and literal text"

-- | Find the text mask for a prefix with a completion.
afterText :: Mask TextToken term -> String -> Maybe (Mask TextToken term)
afterText start = either (const Nothing) Just . foldM maskStep start . map Character

-- | All offered original token IDs in ascending order, including EOS.
offeredAt :: Vocabulary Int TextToken -> Maybe (Mask TextToken term) -> [Int]
offeredAt entries = maybe [] (map fst . maskNext . vocabularyMask entries)

-- | Ask the CFTA cursor about the candidate token IDs.
filteredAt :: IntMap.IntMap [TextToken] -> Maybe (Mask TextToken term) -> [Int] -> [Int]
filteredAt _ Nothing _ = []
filteredAt entries (Just state) candidates =
    [token | token <- candidates, Just spelling <- [IntMap.lookup token entries], isRight (foldM maskStep state spelling)]

-- | Read one line of ascending, comma-separated candidate IDs.
readCandidates :: String -> IO [Int]
readCandidates "" = pure []
readCandidates text = maybe (die "bad candidate list") pure $ readMaybe ("[" <> text <> "]")

{- | Prepare the character-prefix states once. Each timed batch queries the
selected mask for each state. The first batch also forces lazy setup.
-}
benchmark :: Int -> (Maybe (Mask TextToken term) -> [Int] -> [Int]) -> Mask TextToken term -> [(String, [Int])] -> IO ()
benchmark repetitions offered start queries = do
    _ <- evaluate $ sum [length prefix + length candidates | (prefix, candidates) <- queries]
    batch <- newIORef ([(afterText start prefix, candidates) | (prefix, candidates) <- queries])
    let row total (state, candidates) = foldl' (\h i -> h + fromIntegral i + 1) total (offered state candidates)
        -- Reading the batch in IO keeps the checksum from being shared.
        run = readIORef batch >>= evaluate . foldl' row (0 :: Word64)
    before <- getCPUTime
    checksum <- run
    warmed <- getCPUTime
    replicateM_ repetitions $ do
        actual <- run
        unless (actual == checksum) $ die "mask checksum changed"
    finished <- getCPUTime
    putStrLn $
        unwords
            [ "queries=" <> show (length queries)
            , "repeats=" <> show repetitions
            , "first_batch_cpu_ns=" <> show ((warmed - before) `div` 1000)
            , "warm_total_cpu_ns=" <> show ((finished - warmed) `div` 1000)
            , "checksum=" <> show checksum
            , "shared=vocabulary,prepared-prefixes"
            ]

-- | The syntax prefilter may reject entries. CFTA still checks the guard.
selfTest :: IO ()
selfTest = do
    plain <- startMask True 3 False
    strict <- startMask True 3 True
    let entries = IntMap.fromList [(1, [Character 'a']), (2, [Character 'b']), (3, [EndOfText])]
        allEntries = vocabulary (IntMap.toAscList entries)
        state = afterText strict "a+"
    unless
        ( offeredAt allEntries (afterText plain "a+") == [1, 2]
            && filteredAt entries state [1, 2] == [1]
            && null (filteredAt entries state [])
            && filteredAt entries (afterText strict "a+a") [3] == [3]
            && null (filteredAt entries (afterText strict "a+b") [3])
        )
        $ die "prefilter or equal-child mask mismatch"

-- | Use the normal vocabulary trie or check only the supplied candidate IDs.
main :: IO ()
main = do
    args <- getArgs
    case args of
        ["SELFTEST"] -> selfTest
        [notation, boundText, vocabFile, prefixFile, candidatesFile, mode]
            | notation `elem` ["infix", "prefix"]
            , Just bound <- readMaybe boundText
            , bound > 0 -> do
                entries <- readVocabulary vocabFile
                prefixes <- lines <$> readFile prefixFile
                start <- startMask (notation == "infix") (Size bound) True
                let trie = vocabulary (IntMap.toAscList entries)
                (candidates, offered) <- case candidatesFile of
                    "-" -> pure (replicate (length prefixes) [], \state _ -> offeredAt trie state)
                    _ -> do
                        cs <- traverse readCandidates . lines =<< readFile candidatesFile
                        unless (length cs == length prefixes) $ die "prefix and candidate sheet lengths differ"
                        pure (cs, filteredAt entries)
                let queries = zip prefixes candidates
                if mode == "MASK"
                    then forM_ queries $ \(prefix, cs) ->
                        putStrLn $ intercalate "," $ map show $ offered (afterText start prefix) cs
                    else case readMaybe mode of
                        Just repetitions | repetitions > 0 -> benchmark repetitions offered start queries
                        _ -> die "expected MASK or a positive repetition count"
        _ -> die "CursorPrefilter infix|prefix SIZE VOCAB PREFIXES CANDIDATES|- MASK|REPEATS, or CursorPrefilter SELFTEST"
