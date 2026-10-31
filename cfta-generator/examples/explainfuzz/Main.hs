-- | Learn a finite query distribution, condition it, and draw valid queries.
module Main (main) where

import Control.Monad (forM_, unless)
import Data.Either (isLeft)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Ratio ((%))
import qualified Data.Set as Set
import System.Environment (getArgs)
import System.Exit (die)
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Gen as QCGen
import qualified Test.QuickCheck.Random as QCRandom
import Text.Printf (printf)
import Text.Read (readMaybe)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Index (Rank (..))
import Data.CFTA.Sized.Prefix (
    Completions,
    Token,
    completionTerms,
    completionWeight,
    prefixCompletions,
    rankCompletion,
    rankWeighted,
    unrankCompletion,
    unrankWeighted,
    weightedTotal,
    withWeights,
 )
import Data.CFTA.Sized.Prefix.Parents (
    Context,
    Parented,
    Reach (..),
    labelParents,
    rootContext,
    unlabelParents,
    withParents,
 )
import qualified Data.CFTA.Sized.Prefix.Train as Train
import Data.CFTA.Term (Term (..))

-- | The structural requirements supported by this example.
data Requirement = AnyQuery | Grouped | Filtered | GroupedFiltered | Impossible
    deriving (Eq, Ord, Show)

-- | A token with its parent and left-sibling context.
type Label = Parented String

-- | The finite states produced by the context annotation.
type LabelState = (String, Context String, Maybe (Token String))

-- | Learned potentials and their full finite support.
data Learned = Learned
    { learnedGraph :: FTA.FTA LabelState Label Constraint
    , learnedWeights :: Train.LogWeights Label
    , learnedSpace :: Completions Label
    }

-- | The maximum node count of every query in this finite grammar.
bound :: Int
bound = 8

-- | The context used for fitting and all subsequent queries.
reach :: Reach
reach = Reach 1 True

-- | Parse the command before fitting the example corpus.
main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        [] -> demo Grouped 7 12
        ["demo"] -> demo Grouped 7 12
        ["check"] -> check
        ["--help"] -> putStrLn usage
        ["sample", requested, seedText, countText] -> do
            requirement <- either die pure $ parseRequirement requested
            case (readMaybe seedText, readMaybe countText) of
                (Just seed, Just count)
                    | seed >= 0 && seed <= 1000000 && count >= 1 && count <= 10000 ->
                        demo requirement seed count
                _ -> die $ "Seed must be 0..1000000 and count must be 1..10000.\n" <> usage
        _ -> die usage

-- | The available consumer operations.
usage :: String
usage =
    "Usage: cfta-explainfuzz [demo | sample REQUIREMENT SEED COUNT | check | --help]\nRequirements: any, grouped, filtered, grouped-filtered, impossible"

-- | Decode the closed requirement menu without accepting unknown names.
parseRequirement :: String -> Either String Requirement
parseRequirement name = case name of
    "any" -> Right AnyQuery
    "grouped" -> Right Grouped
    "filtered" -> Right Filtered
    "grouped-filtered" -> Right GroupedFiltered
    "impossible" -> Right Impossible
    _ -> Left $ "Unknown requirement: " <> name <> "\n" <> usage

-- | Build the query grammar, optionally restricted at its filter and grouping states.
grammar :: Requirement -> FTA.FTA String String Constraint
grammar requirement =
    either (error . show) id $
        FTA.mkFTA
            "query"
            [ ("query", if requirement == Impossible then [] else [node "query" ["filter", "tail"]])
            , ("filter", [node "all" [] | requirement `notElem` [Filtered, GroupedFiltered]] <> [node "where" ["predicate"]])
            , ("predicate", [node "active" [], node "salary_gt" ["number"]])
            , ("tail", [node "plain" [] | requirement `notElem` [Grouped, GroupedFiltered]] <> [node "group" ["column", "having"]])
            , ("column", [node "department" [], node "role" []])
            , ("having", [node "no_having" [], node "having" ["number"]])
            , ("number", [node number [] | number <- ["10", "50", "100"]])
            ]
  where
    node symbol children = FTA.Transition symbol children noConstraint

-- | A small example corpus with 125 query occurrences and six distinct queries.
corpus :: [Term String]
corpus =
    concat
        [ replicate 50 $ query (Node "all" []) (Node "plain" [])
        , replicate 30 $ query (Node "where" [Node "active" []]) (group "department" $ Node "no_having" [])
        , replicate 20 $ query (salary "50") (group "department" $ having "10")
        , replicate 10 $ query (salary "100") (group "role" $ having "50")
        , replicate 5 $ query (Node "all" []) (group "role" $ Node "no_having" [])
        , replicate 10 $ query (salary "10") (Node "plain" [])
        ]
  where
    query predicate tailTerm = Node "query" [predicate, tailTerm]
    salary number = Node "where" [Node "salary_gt" [Node number []]]
    group column havingTerm = Node "group" [Node column [], havingTerm]
    having number = Node "having" [Node number []]

-- | Fit accepted examples once. Reject all invalid or oversized examples explicitly.
train :: [Term String] -> Either String Learned
train examples
    | null examples = Left "The training corpus is empty."
    | any ((> bound) . length . foldr (:) []) examples = Left "A training term exceeds the node bound."
    | any (not . FTA.accepts (grammar AnyQuery)) examples = Left "A training term is outside the query grammar."
    | otherwise = do
        labelled <- note "The query grammar cannot be context-labelled." $ withParents reach rootContext $ grammar AnyQuery
        weights <- note "The bounded fit failed." $ Train.distill labelled bound $ map (labelParents reach rootContext) examples
        unless (all (\value -> finite value && finite (exp value) && exp value > 0) $ Map.elems weights) $
            Left "The fit produced a non-finite or non-positive potential."
        space <- either (Left . show) Right $ prefixCompletions (fromIntegral bound) labelled
        weighted <- note "The fitted potentials cannot be converted to rational weights." $ Train.withLogWeights weights space
        pure $ Learned labelled weights weighted

-- | Restrict the support while retaining the fitted labels and potentials.
condition :: Requirement -> Learned -> Either String (Completions Label)
condition requirement learned = do
    let restricted = FTA.intersectWith match (\_ _ -> noConstraint) (learnedGraph learned) (grammar requirement)
        match labelled symbol = if fst (fst labelled) == symbol then Just labelled else Nothing
    space <- either (Left . show) Right $ prefixCompletions (fromIntegral bound) restricted
    weighted <-
        note "The fitted weights do not apply to the restricted support." $ Train.withLogWeights (learnedWeights learned) space
    if completionWeight weighted > 0
        then Right weighted
        else Left "The requirement has no positive-mass query within the node bound."

-- | Convert an optional library result to an explicit error.
note :: String -> Maybe value -> Either String value
note message = maybe (Left message) Right

-- | Check numerical fit results before converting them to rational weights.
finite :: Double -> Bool
finite value = not (isNaN value || isInfinite value)

-- | Give every finite completion its exact probability from its weighted interval.
probabilities :: (Ord symbol) => Completions symbol -> Map.Map (Term symbol) Rational
probabilities space =
    Map.fromList
        [ (term, width % total)
        | term <- completionTerms space
        , Just (_, width) <- [interval term]
        ]
  where
    total = weightedTotal space
    interval = rankWeighted space

-- | Draw ranks with a fixed seed. The decoder retains its tables across all draws.
sample :: Int -> Int -> Completions Label -> [Term Label]
sample seed count space = QCGen.unGen (QC.vectorOf count draw) (QCRandom.mkQCGen seed) 30
  where
    total = weightedTotal space
    decode = unrankWeighted space
    draw = fromMaybe (error "A weighted rank below the total must decode.") . decode <$> QC.chooseInteger (0, total - 1)

-- | Test the structural requirement independently of the event automaton.
satisfies :: Requirement -> Term String -> Bool
satisfies requirement (Node "query" [filterTerm, tailTerm]) = case requirement of
    AnyQuery -> True
    Grouped -> grouped
    Filtered -> filtered
    GroupedFiltered -> grouped && filtered
    Impossible -> False
  where
    grouped = case tailTerm of Node "group" _ -> True; _ -> False
    filtered = case filterTerm of Node "where" _ -> True; _ -> False
satisfies _ _ = False

-- | Render each query AST to one SQL statement for the documented employees schema.
render :: Term String -> Maybe String
render (Node "query" [filterTerm, tailTerm]) = do
    wherePart <- case filterTerm of
        Node "all" [] -> Just ""
        Node "where" [Node "active" []] -> Just " WHERE active = TRUE"
        Node "where" [Node "salary_gt" [number]] -> (" WHERE salary > " <>) <$> literal number
        _ -> Nothing
    (projection, groupPart) <- case tailTerm of
        Node "plain" [] -> Just ("COUNT(*)", "")
        Node "group" [Node column [], havingTerm] | column `elem` ["department", "role"] -> do
            havingPart <- case havingTerm of
                Node "no_having" [] -> Just ""
                Node "having" [number] -> (" HAVING COUNT(*) > " <>) <$> literal number
                _ -> Nothing
            Just (column <> ", COUNT(*)", " GROUP BY " <> column <> havingPart)
        _ -> Nothing
    Just $ "SELECT " <> projection <> " FROM employees" <> wherePart <> groupPart <> ";"
  where
    literal (Node number []) | number `elem` ["10", "50", "100"] = Just number
    literal _ = Nothing
render _ = Nothing

-- | Sum distinct weighted derivation trees when two trees render to the same output.
ambiguousOutputProbabilities :: Either String (Map.Map String Rational)
ambiguousOutputProbabilities = do
    let derivations = [Node "left_parse" [Node "x" []], Node "right_parse" [Node "x" []], Node "only_parse" [Node "y" []]]
        weight symbol = case symbol of "left_parse" -> 2; "right_parse" -> 3; _ -> 1
    space <- either (Left . show) Right $ prefixCompletions 2 $ FTA.fromTerms derivations
    weighted <- note "The derivation weights must be non-negative." $ withWeights weight space
    pure $
        Map.fromListWith
            (+)
            [(output, probability) | (Node _ [Node output []], probability) <- Map.toList $ probabilities weighted]

-- | Report the event probability and sample the conditioned query distribution.
demo :: Requirement -> Int -> Int -> IO ()
demo requirement seed count = do
    learned <- either die pure $ train corpus
    selected <- either die pure $ condition requirement learned
    let base = learnedSpace learned
        eventProbability = completionWeight selected / completionWeight base
        distribution = probabilities selected
    printf
        "Training examples: %d; valid query ASTs: %d; conditioned ASTs: %d\n"
        (length corpus)
        (length $ completionTerms base)
        (length $ completionTerms selected)
    printf
        "Requirement: %s; learned probability: %.9f; seed: %d\n"
        (show requirement)
        (fromRational eventProbability :: Double)
        seed
    putStrLn "Conditional probabilities below are rounded for display. Sampling uses exact rational weights."
    forM_ (sample seed count selected) $ \term -> do
        query <- maybe (die "A sampled query could not be rendered.") pure $ render $ unlabelParents term
        printf "%.9f  %s\n" (fromRational $ distribution Map.! term :: Double) query
    outputs <- either die pure ambiguousOutputProbabilities
    putStrLn $
        "Ambiguous-output fixture: " <> show (Map.toList outputs) <> " (parse masses for x are 2 and 3; y has mass 1)."

-- | Check every query, each nonempty event, exact conditioning, ranks, and replay.
check :: IO ()
check = do
    learned <- either die pure $ train corpus
    let base = learnedSpace learned
        listed = completionTerms base
        source = map unlabelParents listed
        baseProbabilities = probabilities base
        oversized = foldr (\_ term -> Node "padding" [term]) (Node "all" []) [1 .. bound]
    unless (length source == 45 && Set.size (Set.fromList source) == 45 && sum baseProbabilities == 1) $
        die "The full query support or its probability mass is wrong."
    rendered <- maybe (die "A valid query failed to render.") pure $ traverse render source
    unless (Set.size (Set.fromList rendered) == 45) $ die "Two query ASTs rendered to the same SQL output."
    unless
        ( isLeft (train [])
            && isLeft (train [Node "unknown" []])
            && isLeft (train [oversized])
            && isLeft (condition Impossible learned)
        ) $
        die "An empty corpus, invalid or oversized term, or impossible requirement was accepted."
    forM_ [AnyQuery, Grouped, Filtered, GroupedFiltered] $ \requirement -> do
        selected <- either die pure $ condition requirement learned
        let terms = completionTerms selected
            expected = filter (satisfies requirement . unlabelParents) listed
            eventProbability = completionWeight selected / completionWeight base
            distribution = probabilities selected
            interval = rankWeighted selected
            decode = unrankWeighted selected
            intervals = [pair | term <- terms, Just pair <- [interval term]]
            draws = sample 19 64 selected
        unless (sort terms == sort expected && eventProbability == sum [baseProbabilities Map.! term | term <- expected]) $
            die "The condition changed support or event probability."
        unless
            (sum distribution == 1 && all (\term -> distribution Map.! term == baseProbabilities Map.! term / eventProbability) terms)
            $ die "Conditioning changed relative learned weights."
        unless
            (map fst intervals == scanl (+) 0 (init $ map snd intervals) && sum (map snd intervals) == weightedTotal selected)
            $ die "The weighted intervals do not tile the total."
        forM_ (zip [0 ..] terms) $ \(rank, term) -> do
            unless (rankCompletion selected term == Just (Rank rank) && unrankCompletion selected (Rank rank) == Just term) $
                die "A completion rank did not round-trip."
            case interval term of
                Just (start, width) | width > 0 && decode start == Just term && decode (start + width - 1) == Just term -> pure ()
                _ -> die "A weighted interval did not round-trip."
        unless
            ( draws == sample 19 64 selected
                && all (\term -> FTA.accepts (grammar AnyQuery) (unlabelParents term) && satisfies requirement (unlabelParents term)) draws
            )
            $ die "A seeded draw failed replay, validity, or the condition."
    grouped <- either die pure $ condition Grouped learned
    unless (completionWeight grouped / completionWeight base < 3 / 4) $
        die "The learned distribution did not depart from the uniform grouping probability of 8/9."
    outputs <- either die pure ambiguousOutputProbabilities
    unless (outputs == Map.fromList [("x", 5 / 6), ("y", 1 / 6)]) $
        die "Distinct derivation masses were not added for a shared output."
    putStrLn
        "check: 45 unique SQL outputs; four exact conditional distributions; rank intervals; deterministic valid draws; impossible event; summed-output mass passed"
