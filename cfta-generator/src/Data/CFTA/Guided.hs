{- | Guided search: a search over the terms of a language whose steps a scorer
scores, under the mask. The search writes a term one token at a time, and
each prefix stays inside the language. Machine learning calls this
constrained decoding.

The search reads only the 'Mask' of each prefix ("Data.CFTA.Mask"), so one
search runs on masks with different tokens. In
'Data.CFTA.Mask.completionsMask', a token is a symbol with its number of
children, and a prefix is a list of tokens in preorder, as in
"Data.CFTA.Sized.Prefix". The 'Scorer' is a function from a prefix to the
scores of the next tokens: log-scores, which need no normalization. A token
that the scorer does not score has the score minus infinity.

At each prefix, the search reads the offered tokens of the mask
('maskNext'). The search never writes a token that the mask does not offer,
and it never writes an undecided token ('maskUndecided'). The step
log-probability of an offered token is its score minus the log of the sum of
the exponentials of the scores of the offered tokens: the scores, normalized
over the mask ('MaskOnly'). With 'WeighCompletions', the score of each
offered token gets the log of its probability in 'maskNext' before the
normalization. In 'Data.CFTA.Mask.completionsMask', this probability is the
weight of the completions after the token, divided by the weight of the
completions of the prefix. This is the weight of the grammatical completions
of Park, Wang, Berg-Kirkpatrick, Polikarpova, and D'Antoni, /Grammar-Aligned
Decoding/, NeurIPS 2024 (arXiv:2405.21047). It is exact for weights that are
a product over the nodes, not for the distribution of a language model. The
total log-score of a prefix is the sum of the step log-probabilities of its
tokens.

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

A complete prefix is a prefix with a term in 'maskTerms'. Each of its terms
is a found term with the total log-score of the prefix.

'repair' continues a sequence of tokens that the mask refuses: it keeps the
longest prefix of the sequence whose tokens the masks offer ('maskStep'), and
searches from that prefix.

A dead end is a prefix that is not complete and has no token with a finite
step log-probability. In 'Data.CFTA.Mask.completionsMask' of an automaton
without constraints, each offered token has a completion within the size
bound, so the mask alone gives no dead end. A dead end comes from the scorer,
when it scores no offered token, and with guards, at a prefix whose tokens are
all undecided: the solver accepts no completion of the prefix. At a dead end,
the search takes the best open prefix.

A 'MaskCache' keeps the 'Mask' of each prefix that a search opens. The fields
of a 'Mask' value are lazy, so each field is computed once, when a search
first reads it. 'guide' takes a cache and gives it back with the prefixes that
it opened, so a later search on the same language reads the masks of the
prefixes that it has seen. Use a cache for the masks of one language, with one
set of weights and one kind of token.

The trace has one 'Visit' for each prefix that the search visits. The search
does not visit a complete prefix: it adds the terms of the prefix to the found
terms.

"Data.CFTA.Guided.Model" has the 'Scorer' of a trained model, which needs no
outside model. 'cachedScorer' wraps a scorer with a memory, so that the
scorer answers once for each prefix.
-}
module Data.CFTA.Guided (
    Scorer,
    cachedScorer,
    Weighing (..),
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

import Data.IORef (atomicModifyIORef', newIORef, readIORef)
import Data.List (sortOn)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Ord (Down (..))
import GHC.Clock (getMonotonicTimeNSec)

import Data.CFTA.Mask (Mask (..), Refusal)

-- | A scorer: the log-scores of the next tokens after a prefix, the first token of the prefix first.
type Scorer token = [token] -> IO [(token, Double)]

{- | A scorer with a memory: it calls the given scorer once for each prefix,
and gives the kept result for a prefix that it has seen. The memory grows with
the number of prefixes. Use one cached scorer for one scorer, so for one
language and one model. The memory is safe when threads share it, but two
threads that ask for the same new prefix at the same time can both call the
given scorer.
-}
cachedScorer :: (Ord token) => Scorer token -> IO (Scorer token)
cachedScorer scorer = do
    memory <- newIORef Map.empty
    pure $ \prefix -> do
        kept <- Map.lookup prefix <$> readIORef memory
        case kept of
            Just scores -> pure scores
            Nothing -> do
                scores <- scorer prefix
                atomicModifyIORef' memory $ \known -> (Map.insert prefix scores known, ())
                pure scores

-- | What a step adds to the score of each offered token before the normalization.
data Weighing
    = -- | Zero: the step log-probabilities are the scores, normalized over the mask.
      MaskOnly
    | {- | The log of the probability of the token in 'maskNext'. In
      'Data.CFTA.Mask.completionsMask', this probability uses the weights of
      the completions. Without 'Data.CFTA.Sized.Prefix.withWeights', each
      symbol has the weight one, so the probability is the number of the
      completions after the token, divided by the number of the completions of
      the prefix.
      -}
      WeighCompletions
    deriving (Eq, Show)

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
    {- ^ The number of found terms to stop after. The search stops when the
    number of found terms reaches this limit, and a complete prefix with more
    than one term, such as a text that two terms have, gives all its terms, so
    the result can have more terms than the limit.
    -}
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
data Visit token = Visit
    { visitPrefix :: [token]
    -- ^ The prefix, the first token first.
    , visitMask :: [token]
    -- ^ The offered tokens of the mask ('maskNext'), in ascending order.
    , visitUndecided :: [token]
    -- ^ The undecided tokens of the mask ('maskUndecided'), in ascending order. The search does not write them.
    , visitScores :: [(token, Double)]
    -- ^ The scores of the scorer, as the scorer gave them, also for tokens outside the mask.
    , visitSteps :: [(token, Double)]
    -- ^ The step log-probability of each offered token: minus infinity for a token without a finite score.
    , visitChoice :: Maybe token
    {- ^ The token with the highest step log-probability, the first of equal
    tokens. 'Greedy' continues with it. 'Nothing' at a dead end.
    -}
    }
    deriving (Eq, Show)

-- | The result of a guided search.
data Guided token term = Guided
    { guidedTerms :: [(term, Double)]
    -- ^ The terms of the complete prefixes, each with its total log-score, in the order that the search found them.
    , guidedTrace :: [Visit token]
    -- ^ The visits, in order.
    , guidedStop :: Stop
    }
    deriving (Eq, Show)

-- | The masks of prefixes of one language, by prefix ('maskPrefix').
newtype MaskCache token term = MaskCache (Map [token] (Mask token term))

-- | A cache without a prefix.
emptyMaskCache :: MaskCache token term
emptyMaskCache = MaskCache Map.empty

-- | The number of prefixes in a cache.
maskCacheSize :: MaskCache token term -> Int
maskCacheSize (MaskCache masks) = Map.size masks

-- | The state of a search.
data Guiding token term = Guiding
    { guidingOpen :: Map (Down Double, Int) [token]
    -- ^ The open prefixes, by total log-score and then by the order in which they opened.
    , guidingMasks :: Map [token] (Mask token term)
    -- ^ The mask cache.
    , guidingTotals :: Map [token] Double
    -- ^ The total log-score of each prefix that the search opened.
    , guidingOpened :: !Int
    , guidingVisits :: !Int
    , guidingFound :: [(term, Double)]
    -- ^ The found terms, the last first.
    , guidingTrace :: [Visit token]
    -- ^ The visits, the last first.
    }

{- | Search the terms of a language with the scores of the scorer, from the
prefix of a mask, with a 'Weighing' and a mask cache. Each found term is a
term of a complete prefix ('maskTerms'). In 'Data.CFTA.Mask.completionsMask',
a found term is a term that the automaton accepts within the size bound. The
result has the cache with the masks of the prefixes that the search opened.
-}
guide ::
    (Ord token) =>
    Strategy ->
    SearchLimits ->
    Weighing ->
    Scorer token ->
    MaskCache token term ->
    Mask token term ->
    IO (Guided token term, MaskCache token term)
guide strategy limits weighing scorer (MaskCache cache) start = do
    begin <- getMonotonicTimeNSec
    let deadline = (\micros -> begin + 1000 * fromIntegral (max 0 micros)) <$> searchMicros limits
        masks = Map.insertWith (\_ known -> known) first start cache
        guiding = Guiding Map.empty masks (Map.singleton first 0) 0 0 [] []
    case strategy of
        Beam width -> level deadline width guiding [first]
        _ -> enter deadline guiding first
  where
    first = maskPrefix start
    finish guiding stop =
        pure
            ( Guided (reverse $ guidingFound guiding) (reverse $ guidingTrace guiding) stop
            , MaskCache $ guidingMasks guiding
            )
    -- Whether the limits stop the search before a visit.
    stopped deadline guiding
        | guidingVisits guiding >= searchVisits limits = pure $ Just VisitLimit
        | otherwise = do
            now <- getMonotonicTimeNSec
            pure $ if maybe False (now >=) deadline then Just OutOfTime else Nothing
    complete guiding prefix = not $ null $ maskTerms $ guidingMasks guiding Map.! prefix
    -- Add the terms of a complete prefix to the found terms. 'Just' the stop when they reach their limit.
    found guiding prefix =
        let terms = maskTerms $ guidingMasks guiding Map.! prefix
            foundTerms = reverse [(term, guidingTotals guiding Map.! prefix) | term <- terms] <> guidingFound guiding
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
    choice; and the search with their masks, their totals, and the trace
    record.
    -}
    visit guiding prefix = do
        let mask = guidingMasks guiding Map.! prefix
            total = guidingTotals guiding Map.! prefix
        scores <- scorer prefix
        let offered = map fst $ maskNext mask
            weighingScore = case weighing of
                MaskOnly -> const 0
                WeighCompletions ->
                    let logProbabilities = Map.fromList [(token, log $ fromRational probability) | (token, probability) <- maskNext mask]
                     in \token -> Map.findWithDefault (-(1 / 0)) token logProbabilities
            steps = stepLogProbabilities weighingScore scores offered
            choice = best steps
            children = [(token, prefix <> [token], total + step) | (token, step) <- steps, not $ isInfinite step]
            -- The mask of a child that the cache does not have yet.
            known masks (token, childPrefix, _)
                | Map.member childPrefix masks = masks
                | otherwise = either (const masks) (\after -> Map.insert childPrefix after masks) $ maskStep mask token
        pure
            ( children
            , choice
            , guiding
                { guidingMasks = foldl known (guidingMasks guiding) children
                , guidingTotals =
                    Map.union (guidingTotals guiding) $ Map.fromList [(childPrefix, score) | (_, childPrefix, score) <- children]
                , guidingVisits = guidingVisits guiding + 1
                , guidingTrace = Visit prefix offered (maskUndecided mask) scores steps choice : guidingTrace guiding
                }
            )

-- | The repair of a sequence of tokens.
data Repaired token term = Repaired
    { repairedRefusal :: Maybe (Int, Refusal)
    {- ^ The place of the first token that the mask does not offer, from zero,
    and the reason; 'Nothing' when the masks offer each token.
    -}
    , repairedSearch :: Guided token term
    -- ^ The search from the longest prefix of the sequence whose tokens the masks offer.
    }
    deriving (Eq, Show)

{- | Repair a sequence of tokens, for example the tokens that a language
model writes without a mask: keep the longest prefix of the sequence whose
tokens the masks offer, and search from that prefix with 'guide'. The first
token that a mask does not offer and the tokens after it go. 'maskStep' gives
the reason for the refusal: the token is rejected, the token is undecided, or
the prefix is a whole term. A sequence that is a complete term has that term
as its first found term, without a visit. The total log-scores of the found
terms count from the end of the kept prefix.
-}
repair ::
    (Ord token) =>
    Strategy ->
    SearchLimits ->
    Weighing ->
    Scorer token ->
    MaskCache token term ->
    Mask token term ->
    [token] ->
    IO (Repaired token term, MaskCache token term)
repair strategy limits weighing scorer cache start tokens = do
    let (refusal, kept) = accepted 0 start tokens
    (search, cache') <- guide strategy limits weighing scorer cache kept
    pure (Repaired refusal search, cache')
  where
    -- The place and the reason of the first refused token, and the mask of the tokens before it.
    accepted _ mask [] = (Nothing, mask)
    accepted place mask (token : rest) = case maskStep mask token of
        Right after -> accepted (place + 1 :: Int) after rest
        Left reason -> (Just (place, reason), mask)

{- | The step log-probability of each token of the mask: its score plus the
value that the 'Weighing' gives, normalized over the tokens of the mask with a
finite sum.
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
