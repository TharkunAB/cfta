{- | Guided search: a search over the terms of a language whose steps a scorer
scores, under the mask. The search writes a term one token at a time, and
each prefix stays inside the language. Machine learning calls this
constrained decoding.

A token is a symbol with its number of children, and a prefix is a list of
tokens in preorder, as in "Data.CFTA.Sized.Prefix". The 'Scorer' is a function
from a prefix to the scores of the next tokens: log-scores, which need no
normalization. A token that the scorer does not score has the score minus
infinity.

At each prefix, the search reads the mask: the tokens of 'nextTokens'. Each
token of the mask has a completion within the size bound, and a token outside
the mask has none, so the search never writes it. The step log-probability of
a token of the mask is its score minus the log of the sum of the exponentials
of the scores of the tokens of the mask: the scores, normalized over the
mask. With weights (non-negative, as 'withWeights' needs them), the score of each
token of the mask gets the log of its 'tokenProbability' before the
normalization: the weight of the
completions after the token, divided by the weight of the completions of the
prefix. This is the weight of the grammatical completions of Park, Wang,
Berg-Kirkpatrick, Polikarpova, and D'Antoni, /Grammar-Aligned Decoding/,
NeurIPS 2024 (arXiv:2405.21047). It is exact for weights that are a product
over the nodes, not for the distribution of a language model. The total
log-score of a prefix is the sum of the step log-probabilities of its tokens.

Each step log-probability is at most zero, so the total log-score of a prefix
never goes up when the prefix grows. 'BestFirst' takes the open prefix with
the highest total log-score each time, so it finds the complete terms in
descending order of their total log-scores: the first @k@ found terms are
the @k@ best terms. 'Greedy' continues with the best token after each visit,
and takes the best open prefix only after a found term or at a dead end.
@'Beam' width@ goes one depth at a time: it visits each prefix of the beam,
keeps the @width@ children with the highest total log-scores (the first of
equal children), and stops when the beam is empty. The search finds the terms
of each complete prefix in the beam. With a width of one it follows the best
token of each step, as 'Greedy' does until its first found term; with a width
that holds every prefix, it finds all the terms, by depth.

'repair' continues a sequence of tokens that the mask refuses: it keeps the
longest prefix of the sequence that the mask accepts, and searches its
completions.

A dead end is a prefix that is not complete and has no token with a finite
score. For an automaton without constraints, 'afterToken' keeps only the
stacks of pending states that fit in the remaining size, so each token of the
mask has a completion within the bound: the mask alone gives no dead end. A
dead end comes from the scorer, when it scores no token of the mask, and with
guards, when the solver decides no completion of a token. At a dead end, the
search takes the best open prefix.

A 'MaskCache' keeps the mask state of each prefix that a search opens: its
'Completions', its mask, and, with weights, the 'tokenProbability' of each
token of the mask. Each part is computed once, when a search first reads it.
'guide' takes a cache and gives it back with the prefixes that it opened, so a
later search on the same language reads the mask states of the prefixes that
it has seen. Use a cache with one language and one set of weights.

The trace has one 'Visit' for each prefix that the search visits. The search
does not visit a complete prefix: it adds the terms of the prefix to the found
terms.
-}
module Data.CFTA.Guided (
    Scorer,
    Strategy (..),
    SearchLimits (..),
    Stop (..),
    Visit (..),
    Guided (..),
    guide,

    -- * Repair
    Repaired (..),
    repair,

    -- * Mask caches
    MaskCache,
    emptyMaskCache,
    maskCacheSize,
) where

import Data.List (sortOn)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Ord (Down (..))
import GHC.Clock (getMonotonicTimeNSec)

import Data.CFTA.Refinement.Verdict (Verdict (..))
import Data.CFTA.Sized.Prefix (
    Completions,
    afterToken,
    completeVerdict,
    completionPrefix,
    completionTerms,
    nextTokens,
    tokenProbability,
    withWeights,
 )
import Data.CFTA.Term (Term)

-- | A scorer: the log-scores of the next tokens after a prefix, the first token of the prefix first.
type Scorer symbol = [(symbol, Int)] -> IO [((symbol, Int), Double)]

-- | How the search takes the next prefix.
data Strategy
    = -- | Continue with the best token after each visit.
      Greedy
    | -- | Take the open prefix with the highest total log-score.
      BestFirst
    | -- | Visit the prefixes of a depth, and keep the best children, at most this many.
      Beam !Int
    deriving (Eq, Show)

-- | The limits of a search.
data SearchLimits = SearchLimits
    { searchVisits :: !Int
    -- ^ The most prefixes to visit.
    , searchTerms :: !Int
    -- ^ The number of found terms to stop after.
    , searchMicros :: !(Maybe Int)
    -- ^ The wall-clock time of the search, in microseconds.
    }
    deriving (Eq, Show)

-- | Why a search stops.
data Stop
    = -- | No open prefix remains.
      Exhausted
    | -- | The search found the number of terms of its limit.
      EnoughTerms
    | -- | The search visited the number of prefixes of its limit.
      VisitLimit
    | -- | The wall-clock time of the search passed.
      OutOfTime
    deriving (Eq, Show)

-- | One visit of a prefix.
data Visit symbol = Visit
    { visitPrefix :: [(symbol, Int)]
    -- ^ The prefix, the first token first.
    , visitMask :: [(symbol, Int)]
    -- ^ The tokens of 'nextTokens', in ascending order.
    , visitScores :: [((symbol, Int), Double)]
    -- ^ The scores of the scorer, as the scorer gave them, also for tokens outside the mask.
    , visitSteps :: [((symbol, Int), Double)]
    -- ^ The step log-probability of each token of the mask: minus infinity for a token without a finite score.
    , visitChoice :: Maybe (symbol, Int)
    {- ^ The token with the highest step log-probability, the first of equal
    tokens. 'Greedy' continues with it. 'Nothing' at a dead end.
    -}
    }
    deriving (Eq, Show)

-- | The result of a guided search.
data Guided symbol = Guided
    { guidedTerms :: [(Term symbol, Double)]
    -- ^ The complete terms, each with its total log-score, in the order that the search found them.
    , guidedTrace :: [Visit symbol]
    -- ^ The visits, in order.
    , guidedStop :: Stop
    }
    deriving (Eq, Show)

-- | The mask states of prefixes of one language, by prefix.
newtype MaskCache symbol = MaskCache (Map [(symbol, Int)] (MaskState symbol))

-- | The mask state of a prefix. Each field is computed when a search first reads it.
data MaskState symbol = MaskState
    { stateCompletions :: Completions symbol
    , stateMask :: [(symbol, Int)]
    -- ^ The tokens of 'nextTokens'.
    , stateGrammar :: Map (symbol, Int) Double
    -- ^ The log of the 'tokenProbability' of each token of the mask.
    }

-- | A cache without a prefix.
emptyMaskCache :: MaskCache symbol
emptyMaskCache = MaskCache Map.empty

-- | The number of prefixes in a cache.
maskCacheSize :: MaskCache symbol -> Int
maskCacheSize (MaskCache states) = Map.size states

-- | The mask state of the completions of a prefix.
maskState :: (Ord symbol) => Completions symbol -> MaskState symbol
maskState completions = MaskState completions mask grammar
  where
    mask = map fst $ nextTokens completions
    grammar = Map.fromList [(token, maybe (-(1 / 0)) (log . fromRational) $ tokenProbability completions token) | token <- mask]

-- | The state of a search.
data Guiding symbol = Guiding
    { guidingOpen :: Map (Down Double, Int) [(symbol, Int)]
    -- ^ The open prefixes, by total log-score and then by the order in which they opened.
    , guidingStates :: Map [(symbol, Int)] (MaskState symbol)
    -- ^ The mask cache.
    , guidingTotals :: Map [(symbol, Int)] Double
    -- ^ The total log-score of each prefix that the search opened.
    , guidingOpened :: !Int
    , guidingVisits :: !Int
    , guidingFound :: [(Term symbol, Double)]
    -- ^ The found terms, the last first.
    , guidingTrace :: [Visit symbol]
    -- ^ The visits, the last first.
    }

{- | Search the completions with the scores of the scorer, from the prefix of
the completions, with optional weights for the symbols and a mask cache. Each
found term is a complete term of the completions: a term that the automaton
accepts within the size bound. The result has the cache with the prefixes
that the search opened.
-}
guide ::
    (Ord symbol) =>
    Strategy ->
    SearchLimits ->
    Maybe (symbol -> Rational) ->
    Scorer symbol ->
    MaskCache symbol ->
    Completions symbol ->
    IO (Guided symbol, MaskCache symbol)
guide strategy limits weights scorer (MaskCache cache) start = do
    begin <- getMonotonicTimeNSec
    let deadline = (\micros -> begin + 1000 * fromIntegral (max 0 micros)) <$> searchMicros limits
        states = Map.insertWith (\_ known -> known) first (maskState root) cache
        guiding = Guiding Map.empty states (Map.singleton first 0) 0 0 [] []
    case strategy of
        Beam width -> level deadline width guiding [first]
        _ -> enter deadline guiding first
  where
    root = maybe start (\weight -> fromMaybe (error "guide: a negative weight") $ withWeights weight start) weights
    first = completionPrefix root
    finish guiding stop =
        pure
            ( Guided (reverse $ guidingFound guiding) (reverse $ guidingTrace guiding) stop
            , MaskCache $ guidingStates guiding
            )
    -- Whether the limits stop the search before a visit.
    stopped deadline guiding
        | guidingVisits guiding >= searchVisits limits = pure $ Just VisitLimit
        | otherwise = do
            now <- getMonotonicTimeNSec
            pure $ if maybe False (now >=) deadline then Just OutOfTime else Nothing
    complete guiding prefix = completeVerdict (stateCompletions $ guidingStates guiding Map.! prefix) == Yes
    -- Add a complete prefix to the found terms. 'Just' the stop when they reach their limit.
    found guiding prefix =
        let term = take 1 $ completionTerms $ stateCompletions $ guidingStates guiding Map.! prefix
            foundTerms = [(found', guidingTotals guiding Map.! prefix) | found' <- term] <> guidingFound guiding
            guiding' = guiding{guidingFound = foundTerms}
         in (guiding', if length foundTerms >= searchTerms limits then Just EnoughTerms else Nothing)
    -- Take the best open prefix.
    next deadline guiding = case Map.minView $ guidingOpen guiding of
        Nothing -> finish guiding Exhausted
        Just (prefix, rest) -> enter deadline guiding{guidingOpen = rest} prefix
    -- Enter a prefix: take the terms of a complete prefix, or visit another prefix within the limits.
    enter deadline guiding prefix
        | complete guiding prefix = case found guiding prefix of
            (guiding', Just stop) -> finish guiding' stop
            (guiding', Nothing) -> next deadline guiding'
        | otherwise = do
            limit <- stopped deadline guiding
            case limit of
                Just stop -> finish guiding stop
                Nothing -> do
                    (children, choice, guiding') <- visit guiding prefix
                    let followed = case strategy of
                            Greedy -> choice
                            _ -> Nothing
                        opening = [child | child@(_, childPrefix, _) <- children, Just childPrefix /= fmap ((prefix <>) . pure) followed]
                    case followed of
                        Just token -> enter deadline (open opening guiding') (prefix <> [token])
                        Nothing -> next deadline (open opening guiding')
    -- Put children in the open prefixes.
    open children guiding =
        guiding
            { guidingOpen =
                Map.union (guidingOpen guiding) $
                    Map.fromList
                        [((Down score, guidingOpened guiding + index), childPrefix) | (index, (_, childPrefix, score)) <- zip [0 ..] children]
            , guidingOpened = guidingOpened guiding + length children
            }
    -- One depth of a beam, best first: the terms of complete prefixes, visits of the others, then the best children.
    level deadline width guiding prefixes = go guiding [] prefixes
      where
        go guiding' children [] = case take width $ sortOn (\(index, (_, _, score)) -> (Down score, index)) $ zip [0 :: Int ..] $ reverse children of
            [] -> finish guiding' Exhausted
            kept -> level deadline width guiding' [childPrefix | (_, (_, childPrefix, _)) <- kept]
        go guiding' children (prefix : rest)
            | complete guiding' prefix = case found guiding' prefix of
                (guiding'', Just stop) -> finish guiding'' stop
                (guiding'', Nothing) -> go guiding'' children rest
            | otherwise = do
                limit <- stopped deadline guiding'
                case limit of
                    Just stop -> finish guiding' stop
                    Nothing -> do
                        (grown, _, guiding'') <- visit guiding' prefix
                        go guiding'' (reverse grown <> children) rest
    {- Visit a prefix: call the scorer, and give its children with a finite
    step log-probability, with their totals, in the order of the mask; the
    choice; and the search with their mask states, their totals, and the
    trace record.
    -}
    visit guiding prefix = do
        let state = guidingStates guiding Map.! prefix
            total = guidingTotals guiding Map.! prefix
        scores <- scorer prefix
        let mask = stateMask state
            grammarScore = case weights of
                Nothing -> const 0
                Just _ -> \token -> Map.findWithDefault (-(1 / 0)) token $ stateGrammar state
            steps = stepLogProbabilities grammarScore scores mask
            choice = best steps
            children = [(token, prefix <> [token], total + step) | (token, step) <- steps, not $ isInfinite step]
            -- The mask state of a child that the cache does not have yet.
            known states (token, childPrefix, _)
                | Map.member childPrefix states = states
                | otherwise =
                    maybe states (\after -> Map.insert childPrefix (maskState after) states) $ afterToken (stateCompletions state) token
        pure
            ( children
            , choice
            , guiding
                { guidingStates = foldl known (guidingStates guiding) children
                , guidingTotals =
                    Map.union (guidingTotals guiding) $ Map.fromList [(childPrefix, score) | (_, childPrefix, score) <- children]
                , guidingVisits = guidingVisits guiding + 1
                , guidingTrace = Visit prefix mask scores steps choice : guidingTrace guiding
                }
            )

-- | The repair of a sequence of tokens.
data Repaired symbol = Repaired
    { repairedRejected :: Maybe Int
    -- ^ The place of the first token that the mask refuses, from zero; 'Nothing' when it accepts each token.
    , repairedSearch :: Guided symbol
    -- ^ The search of the completions of the longest prefix of the sequence that the mask accepts.
    }
    deriving (Eq, Show)

{- | Repair a sequence of tokens, for example the tokens that a language
model writes without a mask: keep the longest prefix of the sequence that the
mask accepts (the first token that it refuses and the tokens after it go), and
search the completions of that prefix with 'guide'. A sequence that is a
complete term has that term as its first found term, without a visit. The
total log-scores of the found terms count from the end of the kept prefix.
-}
repair ::
    (Ord symbol) =>
    Strategy ->
    SearchLimits ->
    Maybe (symbol -> Rational) ->
    Scorer symbol ->
    MaskCache symbol ->
    Completions symbol ->
    [(symbol, Int)] ->
    IO (Repaired symbol, MaskCache symbol)
repair strategy limits weights scorer cache start tokens = do
    let (rejected, kept) = accepted 0 start tokens
    (search, cache') <- guide strategy limits weights scorer cache kept
    pure (Repaired rejected search, cache')
  where
    -- The place of the first refused token, and the completions of the tokens before it.
    accepted _ completions [] = (Nothing, completions)
    accepted place completions (token : rest) = case afterToken completions token of
        Just after -> accepted (place + 1 :: Int) after rest
        Nothing -> (Just place, completions)

{- | The step log-probability of each token of the mask: its score plus the
grammar term, normalized over the tokens of the mask with a finite sum.
-}
stepLogProbabilities :: (Ord token) => (token -> Double) -> [(token, Double)] -> [token] -> [(token, Double)]
stepLogProbabilities extra scores mask = [(token, raw token - normalizer) | token <- mask]
  where
    given = Map.fromList scores
    raw token = Map.findWithDefault (-(1 / 0)) token given + extra token
    finite = filter (not . isInfinite) $ map raw mask
    normalizer = case finite of
        [] -> 0
        _ -> let top = maximum finite in top + log (sum [exp (value - top) | value <- finite])

-- | The token with the highest finite value, the first of equal tokens.
best :: [(token, Double)] -> Maybe token
best = fmap fst . foldl pick Nothing . filter (not . isInfinite . snd)
  where
    pick Nothing scored = Just scored
    pick (Just current) scored
        | snd scored > snd current = Just scored
        | otherwise = Just current
