{-# LANGUAGE OverloadedStrings #-}

{- | Learn preferences between fixed pools of GHC-checked programs. The
corpus score is an offset. Shared token corrections maximize the probability
of each preferred program within its own pool. This module does not check
types or establish semantic equivalence between programs.
-}
module Data.CFTA.GHC.Preference (
    PreferenceCase (..),
    Feature,
    PreferenceModel,
    preferenceBase,
    preferenceWeights,
    preferenceGroups,
    fromFitModel,
    trainPreferences,
    scoreProgram,
    tokenScoreShared,
    parsePreferenceModel,
    printPreferenceModel,
    parsePreferenceCases,
    printPreferenceCases,
) where

import Control.Monad (unless, when)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Text.Read (readMaybe)

import qualified Data.CFTA.GHC.Model as Corpus
import Data.CFTA.Gen.Synthesis (Program (..))
import qualified Data.CFTA.Sized.Prefix.Train as Train

-- | The parent symbol, child position, and token symbol of a node.
type Feature = (Text, Int, Text)

-- | One preferred program and the complete supplied pool for its hole.
data PreferenceCase = PreferenceCase
    { caseGroup :: Text
    -- ^ A source group. Keep groups separate when splitting training and evaluation.
    , caseRoot :: (Text, Int)
    -- ^ The root context used by the plugin, including its lambda-body adjustment.
    , caseLocals :: Set.Set Text
    -- ^ The bound names that the plugin classifies as @arg@.
    , caseUses :: Map.Map Text Int
    -- ^ The module's counts of names that the corpus classifies as @var@.
    , casePreferred :: Program
    -- ^ The exact program to prefer. It must occur in the supplied pool.
    , caseCandidates :: [Program]
    -- ^ A finite pool checked by the caller. This module does not call GHC.
    }
    deriving (Eq, Show)

-- | Corpus counts and finite corrections. The constructor stays private.
data PreferenceModel = PreferenceModel
    { preferenceBase :: Corpus.FitModel
    -- ^ The corpus counts used as the score offset during fitting.
    , preferenceWeights :: Map.Map Feature Double
    -- ^ Shared log-score corrections for parent-position-token features.
    , preferenceGroups :: Set.Set Text
    -- ^ Supplied training-group labels. These labels are not verified provenance.
    }
    deriving (Eq, Show)

-- | Use an existing corpus scorer without corrections.
fromFitModel :: Corpus.FitModel -> PreferenceModel
fromFitModel model = PreferenceModel model Map.empty Set.empty

-- | The feature of one token, with the same symbol mapping as the plugin.
feature :: Corpus.FitModel -> (Text, Int) -> Set.Set Text -> Maybe (Text, Int) -> Int -> (Text, Int) -> Feature
feature model (root, rootPosition) locals parent position token =
    ( maybe root (Corpus.symbolOf model locals) parent
    , maybe rootPosition (const position) parent
    , Corpus.symbolOf model locals token
    )

{- | Score tokens with the corpus score and the learned correction. Apply
the function to the model, module counts, root context, and locals once.
Without corrections, this returns the original corpus scorer directly.
-}
tokenScoreShared ::
    PreferenceModel -> Map.Map Text Int -> (Text, Int) -> Set.Set Text -> Maybe (Text, Int) -> Int -> (Text, Int) -> Double
tokenScoreShared (PreferenceModel base weights _) uses root locals
    | Map.null weights = original
    | otherwise = \parent position token ->
        original parent position token + Map.findWithDefault 0 (feature base root locals parent position token) weights
  where
    original = Corpus.tokenScoreShared base uses root locals

-- | Sum a token scorer over a program without changing its application tree.
foldProgram :: (Maybe (Text, Int) -> Int -> (Text, Int) -> value) -> (value -> value -> value) -> Program -> value
foldProgram at combine = go Nothing 0
  where
    go parent position program =
        let (name, arguments) = spine program []
            token = (name, length arguments)
         in foldl' combine (at parent position token) [go (Just token) index child | (index, child) <- zip [0 ..] arguments]
    spine (Var name) arguments = (name, arguments)
    spine (App function argument) arguments = spine function (argument : arguments)

-- | Score a program in the same context as its training case or plugin hole.
scoreProgram :: PreferenceModel -> PreferenceCase -> Program -> Double
scoreProgram model item = foldProgram (tokenScoreShared model (caseUses item) (caseRoot item) (caseLocals item)) (+)

-- | Cache a program's sparse counts and corpus score before optimization.
prepareProgram :: Corpus.FitModel -> PreferenceCase -> Program -> (Map.Map Feature Double, Double)
prepareProgram base item program =
    ( foldProgram
        (\parent position token -> Map.singleton (feature base (caseRoot item) (caseLocals item) parent position token) 1)
        (Map.unionWith (+))
        program
    , scoreProgram (fromFitModel base) item program
    )

{- | Fit shared corrections with the existing L-BFGS optimizer. The positive
step limit includes the initial point. Precision must be finite and
positive. Each case has equal weight. Duplicate programs count once, while
different programs with the same features retain separate mass. A preferred
program must already occur in its supplied pool.

The returned report states why fitting stopped. The corpus model is stored
with the corrections, so the plugin can load the result as one file.
-}
trainPreferences ::
    Int -> Double -> Corpus.FitModel -> [PreferenceCase] -> Either String (PreferenceModel, Train.FitReport Feature)
trainPreferences limit precision base items = do
    unless (finite precision && precision > 0) $ Left "Preference precision must be finite and positive."
    when (null items) $ Left "Supply at least one training case."
    prepared <- traverse prepare items
    let size = fromIntegral (length prepared)
        average = Map.map (/ size) . Map.unionsWith (+)
        observed = average [chosen | (_, chosen, _) <- prepared]
        evaluate weights =
            let rows = [distribution weights candidates | (candidates, _, _) <- prepared]
             in (sum [total - offset | ((total, _), (_, _, offset)) <- zip rows prepared] / size, average (map snd rows))
        oracle =
            Train.Oracle
                { Train.oracleSymbols =
                    Set.toAscList $ Set.unions [Map.keysSet counts | (candidates, _, _) <- prepared, (counts, _) <- candidates]
                , Train.oracleLogPartition = fst . evaluate
                , Train.oracleExpectations = evaluate
                }
    report <- either (Left . show) Right $ Train.fitWithReport limit precision oracle observed Map.empty
    pure (PreferenceModel base (Train.stepWeights $ Train.fitFinalStep report) (Set.fromList $ map caseGroup items), report)
  where
    prepare item = do
        unless (not (Text.null $ fst $ caseRoot item) && snd (caseRoot item) >= 0 && all (>= 0) (caseUses item)) $
            bad item "Empty root parent, negative context position, or negative module-use count."
        let programs = Set.toAscList $ Set.fromList (caseCandidates item)
        unless (casePreferred item `elem` programs) $ bad item "The preferred program is absent from its candidate pool."
        unless (length programs >= 2) $ bad item "Supply at least two distinct candidate programs."
        let candidates = map (prepareProgram base item) programs
            (chosen, offset) = prepareProgram base item (casePreferred item)
        unless (all (finite . snd) candidates) $ bad item "The corpus score is non-finite."
        pure (candidates, chosen, offset)
    bad item message = Left $ Text.unpack (caseGroup item) <> ": " <> message

-- | Stable log-sum-exp and expected sparse counts over one finite pool.
distribution :: Map.Map Feature Double -> [(Map.Map Feature Double, Double)] -> (Double, Map.Map Feature Double)
distribution weights candidates =
    let scores =
            [ offset + sum [count * Map.findWithDefault 0 key weights | (key, count) <- Map.toList counts]
            | (counts, offset) <- candidates
            ]
        largest = maximum scores
        masses = map (exp . subtract largest) scores
        total = sum masses
     in ( largest + log total
        , Map.unionsWith (+) [Map.map (* (mass / total)) counts | (mass, (counts, _)) <- zip masses candidates]
        )

-- | Whether a floating-point value is finite.
finite :: Double -> Bool
finite value = not (isNaN value || isInfinite value)

{- | Write corrections followed by their original corpus counts. Each
correction is a Haskell-readable @(parent, position, symbol, weight)@ tuple.
-}
printPreferenceModel :: PreferenceModel -> Text
printPreferenceModel (PreferenceModel base weights groups) =
    Text.unlines
        ( "fit-preferences 1;"
            : ("groups " <> Text.pack (show $ Set.toAscList groups))
            : [Text.pack $ show (parent, position, symbol, value) | ((parent, position, symbol), value) <- Map.toAscList weights]
        )
        <> Corpus.printFitModel base

-- | Read a preference file or an existing @fit-model 1;@ file.
parsePreferenceModel :: Text -> Either String PreferenceModel
parsePreferenceModel input = case Text.lines input of
    "fit-preferences 1;" : groupRecord : rest -> do
        groups <-
            maybe (Left "fit-preferences: invalid groups record") Right $
                Text.stripPrefix "groups " groupRecord >>= readMaybe . Text.unpack
        let (records, corpus) = break (== "fit-model 1;") rest
        weights <- foldl' readWeight (Right Map.empty) (zip [3 :: Int ..] records)
        base <- Corpus.parseFitModel $ Text.unlines corpus
        pure $ PreferenceModel base weights (Set.fromList groups)
    _ -> fromFitModel <$> Corpus.parseFitModel input
  where
    readWeight result (line, record) = do
        weights <- result
        case readMaybe (Text.unpack record) of
            Just (parent, position, symbol, value)
                | position >= 0 && not (Text.null parent || Text.null symbol) && finite value ->
                    let key = (parent, position, symbol)
                     in if Map.member key weights
                            then Left $ "fit-preferences: duplicate correction at line " <> show line
                            else Right $ Map.insert key value weights
            _ -> Left $ "fit-preferences: invalid correction at line " <> show line

-- | A file record: group, root context, locals, module-use counts, preferred program, and candidate programs.
type CaseRecord = (Text, (Text, Int), [Text], [(Text, Int)], Program, [Program])

-- | Write one complete case per line. The derived 'Show' form preserves specialized component names.
printPreferenceCases :: [PreferenceCase] -> Text
printPreferenceCases items = Text.unlines $ "fit-preference-cases 1;" : map record items
  where
    record item =
        Text.pack $
            show
                ( caseGroup item
                , caseRoot item
                , Set.toAscList (caseLocals item)
                , Map.toAscList (caseUses item)
                , casePreferred item
                , caseCandidates item
                )

{- | Read serialized program records with the derived 'Read' instance of
'Program'. The records contain AST data, not Haskell source expressions.
For a function hole, store the body and its bound names, as the plugin does.
-}
parsePreferenceCases :: Text -> Either String [PreferenceCase]
parsePreferenceCases input = case Text.lines input of
    "fit-preference-cases 1;" : rest ->
        traverse parseRecord [(line, record) | (line, record) <- zip [2 :: Int ..] rest, not (Text.null $ Text.strip record)]
    _ -> Left "Expected the header fit-preference-cases 1;."
  where
    parseRecord (line, record) = case readMaybe (Text.unpack record) :: Maybe CaseRecord of
        Nothing -> Left $ "Invalid preference case at line " <> show line
        Just (group, root, locals, uses, preferred, candidates) -> do
            unless
                (not (Text.null $ fst root) && snd root >= 0 && all ((>= 0) . snd) uses && length uses == Map.size (Map.fromList uses))
                $ Left
                $ "Invalid context or module-use counts at line " <> show line
            pure $ PreferenceCase group root (Set.fromList locals) (Map.fromList uses) preferred candidates
