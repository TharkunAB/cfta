{- | Fit the weights of the completions of a prefix to a corpus.

The weights of "Data.CFTA.Sized.Prefix" give a distribution over the
completions within the size bound. A completion @t@ has the probability

> P(t) = (Π_s w_s ^ n_s(t)) / Z

where @n_s(t)@ is the number of nodes of @t@ with the symbol @s@, and @Z@ is
the total weight of the completions ('completionWeightBy'). With the
log-weights @θ_s = log w_s@, this is an exponential family whose statistics
are the symbol counts. The mean log-likelihood of a corpus is concave in @θ@,
and its gradient is the mean count of each symbol in the corpus minus its
expected count under the weights:

> ∂L / ∂θ_s = mean n_s - E[n_s]

So the fit reads the corpus only through its mean counts ('meanCounts'). The
expected counts come from one pass of the count table in dual numbers
('Dual'): each symbol has its weight and the derivative of the weight by its
log-weight, which is the weight again.

A tree has one node more than it has edges, so the counts of every term
satisfy @Σ_s (arity_s - 1) n_s = -1@. A change of @θ@ in the direction
@(arity_s - 1)@ multiplies the weight of every term by the same number, so it
does not change the distribution, and the gradient is orthogonal to it. Mean
counts that do not satisfy this identity, for example counts with one pseudo
count added to each symbol, give a log-likelihood that grows without bound in
that direction. 'mixCounts' mixes counts that satisfy it.

A completion larger than the bound has the probability zero, so the terms of
a corpus must be completions. A symbol that the corpus does not have drives
its log-weight to minus infinity; mix the counts with the expected counts of
another model ('mixCounts') to keep each log-weight finite.
-}
module Data.CFTA.Sized.Prefix.Train (
    -- * Distill a corpus
    distill,
    distillWithReport,
    DistillReport (..),
    withLogWeights,
    atTemperature,

    -- * The parts
    Dual (..),
    LogWeights,
    Oracle (..),
    completionsOracle,
    automatonOracle,
    constrainedOracle,
    Step (..),
    FitReport (..),
    FitStopReason (..),
    TrainingError (..),
    expectedCounts,
    logPartition,
    meanCounts,
    mixCounts,
    logLikelihood,
    fit,
    fitWithReport,
    logProbability,
    nextTokenDistribution,
) where

import Data.Array (Array, listArray, (!))
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import qualified Data.CFTA.Gen.Internal.Table as Ordinary
import Data.CFTA.Path (ChildIndex (..))
import Data.Functor (void)
import Data.Ratio (approxRational)

import Data.CFTA.Sized.Prefix (
    Completions,
    Token,
    afterToken,
    completionSymbols,
    completionWeightBy,
    nextTokens,
    rankCompletion,
    withWeights,
 )
import Data.CFTA.Term (Term)

{- | A number and its derivative by the log-weight of each symbol, for
forward-mode differentiation. A symbol that the map does not have has the
derivative zero.
-}
data Dual symbol number = Dual !number !(Map.Map symbol number)
    deriving (Eq, Show)

instance (Ord symbol, Num number) => Num (Dual symbol number) where
    Dual left leftDerivatives + Dual right rightDerivatives =
        Dual (left + right) (Map.unionWith (+) leftDerivatives rightDerivatives)
    Dual left leftDerivatives * Dual right rightDerivatives =
        Dual (left * right) (Map.unionWith (+) (Map.map (left *) rightDerivatives) (Map.map (* right) leftDerivatives))
    negate (Dual value derivatives) = Dual (negate value) (Map.map negate derivatives)
    abs (Dual value derivatives) = Dual (abs value) (Map.map (* signum value) derivatives)
    signum (Dual value _) = Dual (signum value) Map.empty
    fromInteger value = Dual (fromInteger value) Map.empty

{- | Fit the symbol weights of an automaton to a corpus of its terms, for the
terms within a size bound: the maximum-likelihood weights of the module, with
an L2 prior of precision @10^-3@ and two pseudo terms of the uniform model
mixed into the counts. The objective is concave. The optimizer uses
'Double' and can stop before its gradient is small. 'distillWithReport'
returns the stop reason and the number of terms retained.

The oracle follows the automaton. Without constraints, unambiguous rows use
'automatonOracle', and ambiguous rows their bottom-up deterministic rows.
With equalities between direct children, the rows must be unambiguous
without their constraints, and 'constrainedOracle' reads their intersections.
Terms that the automaton rejects, or that are larger than the bound, have
the probability zero, so they are left out. 'Nothing' when no term is left,
or when the automaton has another constraint, ambiguity with constraints, or
more than 1024 deterministic states or intersections.
-}
distill ::
    (Ord state, Ord symbol) =>
    FTA.FTA state symbol Constraint -> Int -> [Term symbol] -> Maybe (LogWeights symbol)
distill automaton bound terms = do
    (oracle, counts, _) <- either (const Nothing) Just $ distillationInput automaton bound terms
    pure $ stepWeights $ last $ take 2000 $ fit 1e-3 oracle counts Map.empty

-- | A corpus fit, with the number of terms retained and dropped before fitting.
data DistillReport symbol = DistillReport
    { distillFit :: FitReport symbol
    , distillRetained :: !Int
    , distillDropped :: !Int
    }
    deriving (Show)

{- | Fit with the same objective, filtering, and 2000-step limit as 'distill'.
Return the final step, the stop reason, and the corpus counts. A finite fit
can stop before convergence. An error reports no retained terms, an
unsupported training route, or a numerical failure.
-}
distillWithReport ::
    (Ord state, Ord symbol) =>
    FTA.FTA state symbol Constraint -> Int -> [Term symbol] -> Either TrainingError (DistillReport symbol)
distillWithReport automaton bound terms = do
    (oracle, counts, retained) <- distillationInput automaton bound terms
    report <- fitWithReport 2000 1e-3 oracle counts Map.empty
    pure $ DistillReport report retained (length terms - retained)

-- | Select the existing oracle route and prepare the regularized corpus counts.
distillationInput ::
    (Ord state, Ord symbol) =>
    FTA.FTA state symbol Constraint ->
    Int ->
    [Term symbol] ->
    Either TrainingError (Oracle symbol, Map.Map symbol Double, Int)
distillationInput automaton bound terms = do
    oracle <- maybe (Left UnsupportedTrainingLanguage) Right chooseOracle
    if null kept
        then Left NoRetainedTerms
        else do
            let retained = length kept
                uniform = snd $ oracleExpectations oracle Map.empty
                counts = mixCounts (fromIntegral retained) (meanCounts kept) 2 uniform
            pure (oracle, counts, retained)
  where
    kept = [term | term <- terms, length (foldr (:) [] term) <= bound, FTA.accepts automaton term]
    reached = FTA.transitionTable $ FTA.trim automaton
    unconstrained = all (all ((== noConstraint) . FTA.transitionConstraint)) reached
    unambiguous = Ordinary.unambiguousRows (Map.map (map void) reached)
    chooseOracle
        | unconstrained && unambiguous = Just $ automatonOracle automaton bound
        | unconstrained =
            (\rows -> groupedOracle (Left $ FTA.initialState automaton) (Map.map (map plain) rows) bound)
                <$> Ordinary.deterministicCountingRows (FTA.mapConstraints (const ()) automaton)
        | unambiguous = constrainedOracle automaton bound
        | otherwise = Nothing
    plain transition = (FTA.transitionSymbol transition, [(child, 1) | child <- FTA.transitionChildren transition])

{- | The completions with the weights of log-weights, for the queries of
"Data.CFTA.Sized.Prefix": 'nextTokenWeights', 'tokenProbability' and
'drawCompletion'. Each weight is the exponential of the log-weight as a
'Rational' within a relative error of @10^-9@. A symbol without a log-weight
has the weight one.
-}
withLogWeights :: (Ord symbol) => LogWeights symbol -> Completions symbol -> Maybe (Completions symbol)
withLogWeights logWeights = withWeights weight
  where
    weight symbol = let value = exp (Map.findWithDefault 0 symbol logWeights) in approxRational value (value * 1e-9)

{- | The log-weights of a temperature: each log-weight divided by the
temperature. The probability of a completion is the exponential of its
log-weights times its counts over the total, so at the temperature @T@ it is
its probability to the power @1/T@, renormalized over the completions. The
temperature applies to whole terms, not to each token, and the next-token
probabilities ('nextTokenDistribution') are those of the whole terms. A
temperature above one makes the distribution flatter, and a temperature below
one makes it sharper. Near zero, the draws go to the completions with the
largest weight ('Data.CFTA.Sized.Prefix.bestCompletions'). The temperature
must be positive.
-}
atTemperature :: Double -> LogWeights symbol -> LogWeights symbol
atTemperature temperature = Map.map (/ temperature)

-- | The log-weight of each symbol. A symbol that the map does not have has the log-weight zero: the weight one.
type LogWeights symbol = Map.Map symbol Double

{- | The total weight of the completions, and the expected count of each
symbol in a completion, for a weight of each symbol. The total weight must be
positive.
-}
expectedCounts ::
    (Ord symbol, Fractional number) => (symbol -> number) -> Completions symbol -> (number, Map.Map symbol number)
expectedCounts weight completions = (total, Map.map (/ total) derivatives)
  where
    Dual total derivatives = completionWeightBy dual completions
    dual symbol = Dual (weight symbol) (Map.singleton symbol (weight symbol))

-- | The logarithm of the total weight of the completions under log-weights.
logPartition :: (Ord symbol) => LogWeights symbol -> Completions symbol -> Double
logPartition logWeights = log . completionWeightBy (weightOf logWeights)

-- | The weight of a symbol under log-weights.
weightOf :: (Ord symbol) => LogWeights symbol -> symbol -> Double
weightOf logWeights symbol = exp $ Map.findWithDefault 0 symbol logWeights

-- | The mean number of nodes with each symbol in the terms of a corpus. The corpus must not be empty.
meanCounts :: (Ord symbol) => [Term symbol] -> Map.Map symbol Double
meanCounts terms =
    Map.map (/ fromIntegral (length terms)) $
        Map.fromListWith (+) [(symbol, 1) | term <- terms, symbol <- foldr (:) [] term]

{- | The counts of a corpus of the given size, mixed with the counts of a
number of pseudo terms: the mean counts of the union of the corpus and the
pseudo terms, when the pseudo terms have the given counts. Expected counts of
any weights satisfy the identity of the module, so the mix does too.
-}
mixCounts :: (Ord symbol) => Double -> Map.Map symbol Double -> Double -> Map.Map symbol Double -> Map.Map symbol Double
mixCounts size counts pseudoSize pseudoCounts =
    Map.map (/ (size + pseudoSize)) $
        Map.unionWith (+) (Map.map (* size) counts) (Map.map (* pseudoSize) pseudoCounts)

{- | The mean log-likelihood of a corpus with the given mean counts, and its
gradient by the log-weights.
-}
logLikelihood ::
    (Ord symbol) => Oracle symbol -> Map.Map symbol Double -> LogWeights symbol -> (Double, Map.Map symbol Double)
logLikelihood oracle counts logWeights = (value, gradient)
  where
    (logTotal, expected) = oracleExpectations oracle logWeights
    value = sum [Map.findWithDefault 0 symbol logWeights * count | (symbol, count) <- Map.toList counts] - logTotal
    gradient = Map.unionWith (+) counts (Map.map negate expected)

{- | What a fit reads of a language: its symbols, and for log-weights, the
logarithm of the total weight and the expected count of each symbol.
-}
data Oracle symbol = Oracle
    { oracleSymbols :: [symbol]
    , oracleLogPartition :: LogWeights symbol -> Double
    , oracleExpectations :: LogWeights symbol -> (Double, Map.Map symbol Double)
    }

-- | The oracle of the completions of a prefix, with dual numbers: exact in any number type, and slow for many symbols.
completionsOracle :: (Ord symbol) => Completions symbol -> Oracle symbol
completionsOracle completions =
    Oracle
        { oracleSymbols = Set.toAscList $ Set.fromList $ completionSymbols completions
        , oracleLogPartition = (`logPartition` completions)
        , oracleExpectations = \logWeights ->
            let (total, expected) = expectedCounts (weightOf logWeights) completions in (log total, expected)
        }

{- | The oracle of the terms that an automaton accepts with at most a number of
nodes, by inside-outside on the sizes ('groupedOracle'). The automaton must
be unambiguous, so that the runs are the terms; its constraints are ignored.
-}
automatonOracle :: (Ord state, Ord symbol) => FTA.FTA state symbol constraint -> Int -> Oracle symbol
automatonOracle automaton =
    groupedOracle
        (FTA.initialState automaton)
        ( Map.map
            (map $ \transition -> (FTA.transitionSymbol transition, [(child, 1) | child <- FTA.transitionChildren transition]))
            (FTA.transitionTable $ FTA.trim automaton)
        )

{- | The oracle of the terms within a size bound of an automaton whose
constraints are equalities between direct children, with exact weights: the
intersection rows of "Data.CFTA.Gen.Internal.Table" ('Ordinary.intersectionCountingRows'),
where a class of equal children is one child that fills each position of the
class. 'Nothing' when those rows do not apply: a constraint beyond equalities
between direct children, or more than 1024 intersections. The rows must be
unambiguous without their constraints.
-}
constrainedOracle :: (Ord state, Ord symbol) => FTA.FTA state symbol Constraint -> Int -> Maybe (Oracle symbol)
constrainedOracle automaton bound = do
    rows <- Ordinary.intersectionCountingRows (FTA.transitionTable $ FTA.trim automaton) (FTA.initialState automaton)
    pure $ groupedOracle (Set.singleton $ FTA.initialState automaton) (Map.map (map grouped) rows) bound
  where
    grouped transition = (FTA.transitionSymbol transition, groups transition)
    -- One group for each class, and one for each other position: the child, and the number of positions it fills.
    groups transition =
        [ (child, maybe 1 length $ lookup position firsts)
        | (position, child) <- zip [0 ..] (FTA.transitionChildren transition)
        , position `notElem` later
        ]
      where
        classes = FTA.transitionConstraint transition
        firsts = [(first, members) | members@(ChildIndex first : _) <- classes]
        later = [index | _ : rest <- classes, ChildIndex index <- rest]

{- | Inside-outside on the sizes (Eisner, "Inside-outside and forward-backward
algorithms are just backprop", 2016), over rows whose transitions read groups
of children: each group is a child key whose term fills a number of
positions. The expected counts cost about two passes, whatever the number of
symbols.

A group of r positions holds one term that counts r times, in its size and in
its weight. So the inside weight of a key also depends on a multiplier m: the
total over its terms of each size of the weight to the power m. A transition
weighs w^m, and a group of r positions reads its key with the multiplier m r,
at a size r times as large. The inside weight of a key, a multiplier and a
size sums over the transitions the weight times the convolution of the groups.
The outside weight is the derivative of the total weight by the inside
weight; it flows from each parent to each group through the convolution of
the other groups, so it reads only larger sizes. The expected count of a
symbol sums, over the transitions with the symbol and the multipliers, m times
the weight times the outside weight times the convolution, over the total
weight: the derivative of w^m by the log-weight is m w^m. A multiplier above
the bound reads no term, so the tables are finite.
-}
groupedOracle :: (Ord key, Ord symbol) => key -> Map.Map key [(symbol, [(key, Int)])] -> Int -> Oracle symbol
groupedOracle root rows bound =
    Oracle
        { oracleSymbols = Set.toAscList $ Set.fromList [symbol | (_, symbol, _) <- transitions]
        , oracleLogPartition = \logWeights -> log $ total (tables logWeights)
        , oracleExpectations = expectations
        }
  where
    keyNumber = Map.fromList (zip (Map.keys rows) [0 :: Int ..])
    transitions =
        [ (keyNumber Map.! key, symbol, [(keyNumber Map.! child, factor) | (child, factor) <- groups])
        | (key, row) <- Map.toList rows
        , (symbol, groups) <- row
        ]
    transitionsArray = listArray (0, length transitions - 1) transitions
    byKey = Map.fromListWith (<>) [(key, [index]) | (index, (key, _, _)) <- zip [0 :: Int ..] transitions]
    transitionsOf key = Map.findWithDefault [] key byKey
    groupsOf index = let (_, _, groups) = transitionsArray ! index in groups
    symbolOf index = let (_, symbol, _) = transitionsArray ! index in symbol
    rootNode = (keyNumber Map.! root, 1 :: Int)
    -- The pairs of a key and a multiplier that the root reaches.
    nodes = Set.toList $ reach Set.empty [rootNode]
    reach seen [] = seen
    reach seen (node@(key, multiplier) : pending)
        | Set.member node seen = reach seen pending
        | otherwise =
            reach
                (Set.insert node seen)
                ( [ (child, multiplier * factor)
                  | index <- transitionsOf key
                  , (child, factor) <- groupsOf index
                  , multiplier * factor <= bound
                  ]
                    <> pending
                )
    nodeNumber = Map.fromList (zip nodes [0 :: Int ..])
    sizes = [0 .. bound]
    poweredWeight logWeights symbol multiplier = exp $ fromIntegral multiplier * Map.findWithDefault 0 symbol logWeights
    total (insideAt, _) = sum [insideAt rootNode size | size <- [1 .. bound]]
    -- The inside weights of the nodes, and the convolution of the groups of each transition at each multiplier, all as lazy arrays.
    tables logWeights = (insideAt, convolutionOf)
      where
        insideArray =
            listArray ((0, 0), (length nodes - 1, bound)) [value node size | node <- nodes, size <- sizes] ::
                Array (Int, Int) Double
        insideAt node size = maybe 0 (\number -> insideArray ! (number, size)) (Map.lookup node nodeNumber)
        value (key, multiplier) size
            | size < 1 = 0
            | otherwise =
                sum
                    [ poweredWeight logWeights (symbolOf index) multiplier * convolutionOf (index, multiplier) ! (size - 1)
                    | index <- transitionsOf key
                    ]
        convolutions =
            LazyMap.fromList
                [ ((index, multiplier), convolve insideAt multiplier (groupsOf index))
                | (key, multiplier) <- nodes
                , index <- transitionsOf key
                ]
        convolutionOf entry = convolutions LazyMap.! entry
    -- The convolution of groups at a multiplier, as an array over the sizes: a group of r positions reads its key with r times the multiplier, at r times the size.
    convolve insideAt multiplier = foldr step (listArray (0, bound) (1 : replicate bound 0) :: Array Int Double)
      where
        step (child, factor) rest =
            listArray
                (0, bound)
                [ sum
                    [ insideAt (child, multiplier * factor) part * rest ! (size - factor * part)
                    | multiplier * factor <= bound
                    , part <- [1 .. size `div` factor]
                    ]
                | size <- sizes
                ]
    expectations logWeights = (log grand, Map.map (/ grand) counts)
      where
        built@(insideAt, convolutionOf) = tables logWeights
        grand = total built
        -- For each transition, multiplier and group position, the convolution of the other groups.
        others =
            LazyMap.fromList
                [ ((index, multiplier, position), convolve insideAt multiplier (take position groups <> drop (position + 1) groups))
                | (key, multiplier) <- nodes
                , index <- transitionsOf key
                , let groups = groupsOf index
                , position <- [0 .. length groups - 1]
                ]
        -- Where each node is a group: the transition, its parent node, and the group's position and factor.
        parents =
            Map.fromListWith
                (<>)
                [ ((child, parentMultiplier * factor), [(index, parentKey, parentMultiplier, position, factor)])
                | (parentKey, parentMultiplier) <- nodes
                , index <- transitionsOf parentKey
                , (position, (child, factor)) <- zip [0 :: Int ..] (groupsOf index)
                , parentMultiplier * factor <= bound
                ]
        outsideArray =
            listArray ((0, 0), (length nodes - 1, bound)) [outsideValue node size | node <- nodes, size <- sizes] ::
                Array (Int, Int) Double
        outsideAt node size = outsideArray ! (nodeNumber Map.! node, size)
        outsideValue node size
            | size < 1 = 0
            | otherwise =
                (if node == rootNode then 1 else 0)
                    + sum
                        [ outsideAt (parentKey, parentMultiplier) larger
                            * poweredWeight logWeights (symbolOf index) parentMultiplier
                            * other ! (larger - 1 - factor * size)
                        | (index, parentKey, parentMultiplier, position, factor) <- Map.findWithDefault [] node parents
                        , let other = others LazyMap.! (index, parentMultiplier, position)
                        , larger <- [factor * size + 1 .. bound]
                        ]
        counts =
            Map.fromListWith
                (+)
                [ ( symbolOf index
                  , fromIntegral multiplier
                        * poweredWeight logWeights (symbolOf index) multiplier
                        * sum [outsideAt node size * convolutionOf (index, multiplier) ! (size - 1) | size <- [1 .. bound]]
                  )
                | node@(key, multiplier) <- nodes
                , index <- transitionsOf key
                ]

-- | A step of 'fit': the log-weights, their objective, and the norm of its gradient.
data Step symbol = Step
    { stepWeights :: LogWeights symbol
    , stepObjective :: !Double
    , stepGradientNorm :: !Double
    }
    deriving (Show)

-- | Why the optimizer stopped. 'GradientTolerance' records a stop caused by the gradient tolerance.
data FitStopReason
    = GradientTolerance
    | ObjectiveTolerance
    | LineSearchFailed
    | StepLimit
    deriving (Eq, Show)

-- | A finite final step, the number of steps evaluated, and the stop reason.
data FitReport symbol = FitReport
    { fitFinalStep :: Step symbol
    , fitStepCount :: !Int
    , fitStopReason :: FitStopReason
    }
    deriving (Show)

-- | An invalid input or numerical failure of a reporting fit.
data TrainingError
    = InvalidStepLimit
    | InvalidPrecision
    | InvalidCounts
    | InvalidInitialWeights
    | NonFiniteStep
    | NoRetainedTerms
    | UnsupportedTrainingLanguage
    deriving (Eq, Show)

{- | Run at most the given number of steps with the objective of 'fit'. The
initial point counts as one step. The limit must be positive. The precision
and counts must be finite and nonnegative. Initial log-weights must be
finite. The caller must supply feasible counts for the oracle's language.

The report preserves the optimizer's stop reason. At the limit it does not
start another line search or evaluate another point to discover whether the
stream ends. A stop already known at the final step takes precedence over
'StepLimit'. The limit bounds steps, not the oracle calls of a line search.
Every returned step is checked for finite weights, objective, and gradient
norm. This validation does not change the legacy 'fit' stream.
-}
fitWithReport ::
    (Ord symbol) =>
    Int -> Double -> Oracle symbol -> Map.Map symbol Double -> LogWeights symbol -> Either TrainingError (FitReport symbol)
fitWithReport limit precision oracle counts start
    | limit <= 0 = Left InvalidStepLimit
    | not (finite precision) || precision < 0 = Left InvalidPrecision
    | any (\value -> not (finite value) || value < 0) counts = Left InvalidCounts
    | any (not . finite) start = Left InvalidInitialWeights
    | otherwise = collect 1 $ fitTrace precision oracle counts start
  where
    collect count trace = case trace of
        FitDone step reason -> report count step reason
        FitMore step next
            | not (finiteStep step) -> Left NonFiniteStep
            | count >= limit -> report count step StepLimit
            | otherwise -> case next of
                Left reason -> report count step reason
                Right rest -> collect (count + 1) rest
    report count step reason
        | finiteStep step = Right $ FitReport step count reason
        | otherwise = Left NonFiniteStep

-- | Whether a floating-point value is finite.
finite :: Double -> Bool
finite value = not (isNaN value || isInfinite value)

-- | Whether all numerical fields of a step are finite.
finiteStep :: Step symbol -> Bool
finiteStep step = all finite $ stepObjective step : stepGradientNorm step : Map.elems (stepWeights step)

-- | A fit step with either a known stop or an unevaluated continuation.
data FitTrace symbol
    = FitDone (Step symbol) FitStopReason
    | FitMore (Step symbol) (Either FitStopReason (FitTrace symbol))

{- | Maximize the mean log-likelihood of a corpus with the given mean counts,
minus @precision / 2@ times the squared norm of the log-weights (a Gaussian
prior with that precision), from the given log-weights. The method is L-BFGS
with the ten last steps (Nocedal and Wright, /Numerical Optimization/, 2006,
algorithm 7.4) and a backtracking line search with the Armijo condition. A
positive precision also fixes the arity direction of the module: of the
log-weights with one distribution, the prior prefers the shortest.

The list ends when the norm of the gradient is below @1e-9@, when a step
improves the objective by less than @1e-13@ times its size (the sums in
'Double' stop the gradient near @1e-7@ for some models), or when the line
search finds no step up. Take a prefix of it to bound the work.
-}
fit :: (Ord symbol) => Double -> Oracle symbol -> Map.Map symbol Double -> LogWeights symbol -> [Step symbol]
fit precision oracle counts start = steps $ fitTrace precision oracle counts start
  where
    steps (FitDone step _) = [step]
    steps (FitMore step next) = step : either (const []) steps next

-- | Share the optimizer and its lazy continuations between both public fit APIs.
fitTrace :: (Ord symbol) => Double -> Oracle symbol -> Map.Map symbol Double -> LogWeights symbol -> FitTrace symbol
fitTrace precision oracle counts start = go [] startPoint startValue startGradient
  where
    -- The parameters: each symbol of the language and of the corpus.
    symbols = Set.toAscList $ Set.fromList $ Map.keys counts <> oracleSymbols oracle
    toVector logWeights = [Map.findWithDefault 0 symbol logWeights | symbol <- symbols]
    fromVector = Map.fromList . zip symbols
    -- The objective to minimize, and its gradient.
    loss vector = negate (penalized (fromVector vector))
    penalized logWeights =
        sum [Map.findWithDefault 0 symbol logWeights * count | (symbol, count) <- Map.toList counts]
            - oracleLogPartition oracle logWeights
            - precision / 2 * sum (map (^ (2 :: Int)) (Map.elems logWeights))
    lossAndGradient vector = (negate value, zipWith (\slope weight -> precision * weight - slope) slopes vector)
      where
        logWeights = fromVector vector
        (logLikelihoodValue, gradient) = logLikelihood oracle counts logWeights
        value = logLikelihoodValue - precision / 2 * sum (map (^ (2 :: Int)) vector)
        slopes = [Map.findWithDefault 0 symbol gradient | symbol <- symbols]
    startPoint = toVector start
    (startValue, startGradient) = lossAndGradient startPoint
    go history point value gradient
        | norm < 1e-9 = FitDone here GradientTolerance
        | otherwise = FitMore here $ maybe (Left LineSearchFailed) (Right . next) (search 1)
      where
        here = Step (fromVector point) (negate value) norm
        norm = sqrt $ dot gradient gradient
        quasiNewton = map negate $ twoLoop history gradient
        direction = if dot quasiNewton gradient < 0 then quasiNewton else map negate gradient
        slope = dot direction gradient
        search rate
            | rate < 1e-12 = Nothing
            | loss candidate <= value + 1e-4 * rate * slope = Just candidate
            | otherwise = search (rate / 2)
          where
            candidate = zipWith (+) point (map (* rate) direction)
        next candidate
            | value - value' < 1e-13 * max 1 (abs value) =
                FitDone (Step (fromVector candidate) (negate value') (sqrt $ dot gradient' gradient')) ObjectiveTolerance
            | otherwise = go history' candidate value' gradient'
          where
            (value', gradient') = lossAndGradient candidate
            change = zipWith (-) candidate point
            gradientChange = zipWith (-) gradient' gradient
            history'
                | dot change gradientChange > 1e-12 = take 10 $ (change, gradientChange) : history
                | otherwise = history

-- | The product of the inverse Hessian estimate of L-BFGS with a vector: the two-loop recursion.
twoLoop :: [([Double], [Double])] -> [Double] -> [Double]
twoLoop history vector = foldr second (map (* scale) first) (zip history alphas)
  where
    -- Newest pair first.
    (first, alphas) = foldl firstLoop (vector, []) history
    firstLoop (current, found) (change, gradientChange) =
        let rho = 1 / dot gradientChange change
            alpha = rho * dot change current
         in (zipWith (-) current (map (* alpha) gradientChange), found <> [alpha])
    second ((change, gradientChange), alpha) current =
        let rho = 1 / dot gradientChange change
            beta = rho * dot gradientChange current
         in zipWith (+) current (map (* (alpha - beta)) change)
    scale = case history of
        (change, gradientChange) : _ -> dot change gradientChange / dot gradientChange gradientChange
        [] -> 1

dot :: [Double] -> [Double] -> Double
dot left right = sum $ zipWith (*) left right

{- | The log-probability of a completion under log-weights. 'Nothing' when the
term is not a completion.
-}
logProbability :: (Ord symbol) => LogWeights symbol -> Completions symbol -> Term symbol -> Maybe Double
logProbability logWeights completions term = case rankCompletion completions term of
    Nothing -> Nothing
    Just _ ->
        Just $ sum [Map.findWithDefault 0 symbol logWeights | symbol <- foldr (:) [] term] - logPartition logWeights completions

{- | The probability of each next token after the prefix of the completions,
under log-weights: the weight of the completions after the token over the
weight of the completions. The weight of the prefix is in both, so it
cancels. This is the next-token distribution of the weights as a language
model over tokens in preorder.
-}
nextTokenDistribution :: (Ord symbol) => LogWeights symbol -> Completions symbol -> [(Token symbol, Double)]
nextTokenDistribution logWeights completions =
    [ (token, completionWeightBy weight after / total)
    | (token, _) <- nextTokens completions
    , Just after <- [afterToken completions token]
    ]
  where
    weight = weightOf logWeights
    total = completionWeightBy weight completions
