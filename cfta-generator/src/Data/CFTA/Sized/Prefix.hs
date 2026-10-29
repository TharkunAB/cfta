{- | The completions of a prefix: the terms that a finite tree automaton
accepts within a size bound and whose preorder starts with the prefix.

A token is one node of a term in preorder: its symbol and its number of
children, as in 'Data.CFTA.Template.preorderPrefix'. A prefix is a list of
tokens. A completion of a prefix is an accepted term with at most the bound
of nodes whose preorder starts with the prefix. A 'Completions' value holds
a prefix and answers these queries:

* 'nextTokens': the tokens that can come next, each with the number of
  completions that remain after it.
* 'afterToken': the completions after one more token. The result is
  'Nothing' when no completion remains, so a caller can reject a token at
  once.
* 'isComplete': whether the prefix is itself an accepted term.
* 'completionCount', 'completionTerms', 'unrankCompletion', and
  'sampleCompletion': the completions, counted, listed, unranked, and
  sampled uniformly.

A decoder that writes a term one token at a time can use 'nextTokens' to
reject an invalid token at once, before it writes the rest of the term.

The count of a prefix is the sum of the counts that 'nextTokens' gives, plus
one when the prefix is complete. A complete prefix has no next token.

The queries read the automaton from the root down. Each run of the automaton
on the nodes of a prefix leaves a stack of pending states: the states of the
subterms that the prefix does not reach, in preorder. A completion fills the
pending nodes with terms of the pending states. All the stacks of a prefix
have the same length, because each token removes one pending node and adds
one for each child. The size of a completion is the length of the prefix plus
the sizes of the terms that fill the pending nodes.

The completions are distinct terms, each once, as in "Data.CFTA.Sized". When
the rows of the automaton are unambiguous, each term has at most one run.
Then two stacks have no completion in common, and the count of a stack is the
convolution of the counts of its states. The counts of the states come from
one count table, 'Data.CFTA.Sized.sizedStates'. When the rows are ambiguous,
one term can complete two stacks. Then the queries list the completions and
keep the first place of each term, as 'Data.CFTA.Sized.sizedReference' does.
This is exact, but it is slow for many completions.

The completions are in order of their size, then of their stack, then of the
terms that fill the stack. The term of the first pending node varies
slowest. Each pending node goes through its sizes in ascending order, and
through each size class in the order of "Data.CFTA.Sized". For the empty
prefix, this is the order of 'Data.CFTA.Sized.sized'. The stacks are in
lexicographic order of their states, and the states are in the order of
their 'Ord' instance. The rank of a completion is its place among the
completions of this prefix. It is not the rank of the term in the whole
language.

An automaton with equality constraints takes another route, because a
constraint of a prefix node can relate the terms of two pending nodes. The
queries list the accepted terms up to the bound, from the size classes of
'Data.CFTA.Sized.sizedStates', which check the equality constraints, and keep
the terms that start with the prefix. Each token keeps the completions that
continue with it. This is exact, but the first query lists every accepted
term up to the bound. The completions are in the order of
'Data.CFTA.Sized.sized'.

'prefixCompletions' rejects a guard beyond equality constraints.
'prefixCompletionsWith' takes a solver, an 'Entailment', and lists the terms
of the automaton with each constraint reduced to its equality constraints. The
solver decides each such term: it accepts it ('Yes'), rejects it ('No'), or
does not decide it ('Unknown'). The rejected terms go. A token is offered
('nextTokens') when the solver accepts one of its completions, rejected when
it rejects all of them, and undecided ('undecidedTokens') otherwise. An
undecided token is neither offered nor rejected. The counts, the lists, the
ranks, and the samples cover the accepted completions; 'undecidedTerms' lists
the others.

'prefixCompletionsWith' decides every candidate up to the bound before the
first query. A decoder that walks one path of tokens needs less: 'deciding'
starts the walk, 'decidingStep' adds a token, and 'decidingTokens' gives the
verdict of each next token. They ask the solver only about the candidates that
the prefix can still reach, and only until a verdict is known: a token is
offered at its first accepted candidate. The verdicts that the solver gives
are kept for the whole walk. The next tokens come from the runs of the
automaton on the prefix, not from a list of the candidates, and a constraint
of a prefix node whose paths the prefix fixes is decided once for its whole
run. 'decided' gives the 'Completions' of the current prefix, the same as
'prefixCompletionsWith' and 'afterPrefix' give. A query for counts needs
every candidate decided, so it gains nothing from the walk.

With equality constraints, a query first tries the fillings of the pending
states, up to 'fillingsBeforeProduct' of them. Then it takes its candidates
from an automaton of the terms of each exact size up to the bound, restricted
to the prefix, whose enumerator ("Data.CFTA.Enumeration") solves the
equalities by unification; the walk builds it once, and its later queries use
it at once. A token is offered at the first completion that either route
gives, so the tokens are exact without a list of the terms up to the bound. The counts
are not: an equality class that joins two pending nodes makes the count of
their fillings more than a product of their counts, so 'decided' and the
counts still list the candidates.

'withWeights' gives each symbol a weight, a non-negative 'Rational'. The weight
of a term is the product of the weights of the symbols of its nodes.
'nextTokenWeights' gives the total weight of the completions after each token,
'tokenProbability' the probability of a token after the prefix, and
'sampleWeighted' draws a completion in proportion to its weight. A decoder
that mixes the scores of a model with a grammar needs this mass of the
grammatical completions; see Park, Wang, Berg-Kirkpatrick, Polikarpova, and
D'Antoni, /Grammar-Aligned Decoding/, NeurIPS 2024 (arXiv:2405.21047). Here
the mass is exact for a weight that is a product over the nodes, not for the
distribution of a language model. With unambiguous rows and no constraint,
the weights of a state are a convolution over its transitions, as the counts
are. Otherwise they are sums over the listed completions. Weights on the
symbols, not on the transitions, give each completion one weight, also when
two runs accept it.
-}
module Data.CFTA.Sized.Prefix (
    Completions,
    CompletionsError (..),
    prefixCompletions,
    prefixCompletionsWith,
    afterToken,
    afterPrefix,
    completionPrefix,
    nextTokens,
    undecidedTokens,
    isComplete,
    completeVerdict,
    completionCount,
    completionTerms,
    undecidedTerms,
    unrankCompletion,
    sampleCompletion,

    -- * Weights
    withWeights,
    completionWeight,
    nextTokenWeights,
    tokenProbability,
    sampleWeighted,
    drawCompletion,

    -- * Verdicts on demand
    Deciding,
    deciding,
    decidingWithCap,
    fillingsBeforeProduct,
    decidingPrefix,
    decidingStep,
    decidingTokens,
    decided,
) where

import Control.Monad (foldM, void)
import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import qualified Data.IntMap.Lazy as IntMap
import Data.List (genericDrop, genericIndex, genericLength, genericReplicate, genericTake)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, listToMaybe)
import Data.Ratio (denominator, numerator)
import qualified Data.Set as Set
import qualified Test.QuickCheck as QC

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, constraintPaths, equalities, equalityConstraint, noConstraint, residual)
import qualified Data.CFTA.Enumeration as Enumeration
import Data.CFTA.Equality.Constraint (EqConstraints (EqConstraints), unPathEClass)
import qualified Data.CFTA.Gen.Internal.Table as Ordinary
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Rank (..), Size (..))
import Data.CFTA.Interned (Node (Node), edgeChildren, fromFTA, nodeEdges, setChildren)
import Data.CFTA.Path (ChildIndex (..), Path, getPath, path, unPath)
import Data.CFTA.Refinement.Evaluate (evaluateConstraint)
import Data.CFTA.Refinement.Verdict (Entailment, Verdict (..), andVerdicts, orVerdicts)
import Data.CFTA.Sized (Sized, countOfSize, sizedStates, termsOfSize, unrankOfSize)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Template (Template (..), preorderPrefix, restrict)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | The completions of a prefix within a size bound.
data Completions symbol = Completions
    { completionsPrefix :: [(symbol, Int)]
    -- ^ The prefix, the last token first.
    , completionsBudget :: !Integer
    -- ^ The number of nodes that the pending nodes can have together.
    , completionsWeight :: symbol -> Rational
    -- ^ The weight of each symbol.
    , completionsRoute :: Route symbol
    }

-- | How the queries find the completions of a prefix.
data Route symbol
    = -- | The stacks of pending states that have a completion within the budget, for an automaton without constraints.
      Stacks !(Tables symbol) !(Set.Set [Int])
    | {- | The completions in order, each with its tokens after the prefix and
      whether the solver accepted it ('Yes') or did not decide it ('Unknown'),
      for an automaton with constraints.
      -}
      Listed [(Term symbol, [(symbol, Int)], Verdict)]

-- | The automaton for the queries, with each state as its number.
data Tables symbol = Tables
    { tablesTokens :: IntMap.IntMap (Map.Map (symbol, Int) [[Int]])
    -- ^ The child states of the transitions of each state, by token.
    , tablesMinimum :: IntMap.IntMap Integer
    -- ^ The least size of a term of each state that accepts a term.
    , tablesClasses :: IntMap.IntMap (Sized symbol)
    -- ^ The size classes of each state, built when a query reads them.
    , tablesUnambiguous :: Bool
    -- ^ Whether each term has at most one run from each state.
    , tablesWeights :: IntMap.IntMap [Rational]
    -- ^ The total weight of the terms of each state, for each size from zero, when the rows are unambiguous.
    }

-- | Why the completions of an automaton cannot be built.
data CompletionsError
    = -- | A transition that the initial state reaches has a guard beyond equality constraints.
      GuardedTransition
    deriving (Eq, Show)

{- | The completions of the empty prefix: the terms that the automaton accepts
with at most the given number of nodes.

The result is 'GuardedTransition' when a transition that the initial state
reaches has a guard beyond equality constraints.
-}
prefixCompletions ::
    (Ord state, Ord symbol) => Size -> FTA.FTA state symbol Constraint -> Either CompletionsError (Completions symbol)
prefixCompletions (Size bound) automaton
    | any (any (residual . FTA.transitionConstraint)) reached = Left GuardedTransition
    | all (all ((== noConstraint) . FTA.transitionConstraint)) reached =
        Right $ emptyPrefix bound $ Stacks tables $ Set.fromList $ filter (fits tables bound) [[number initial]]
    | otherwise =
        Right
            $ emptyPrefix bound
            $ Listed [(term, preorder term, Yes) | size <- [1 .. bound], term <- termsOfSize (stateClasses initial) (Size size)]
  where
    reached = FTA.transitionTable $ FTA.trim automaton
    initial = FTA.initialState automaton
    rows = FTA.transitionTable automaton
    numbers = Map.fromList $ zip (Map.keys rows) [0 ..]
    number state = numbers Map.! state
    tables =
        Tables
            { tablesTokens =
                IntMap.fromList
                    [ ( number state
                      , Map.fromListWith
                            (flip (<>))
                            [ ((FTA.transitionSymbol transition, length children), [map number children])
                            | transition <- transitions
                            , let children = FTA.transitionChildren transition
                            ]
                      )
                    | (state, transitions) <- Map.toList rows
                    ]
            , tablesMinimum =
                IntMap.fromList [(number state, size) | (state, Size size) <- Map.toList $ Ordinary.minimumSizes rows]
            , tablesClasses = IntMap.fromList [(number state, stateClasses state) | state <- Map.keys rows]
            , tablesUnambiguous = Ordinary.unambiguousRows $ Map.map (map void) rows
            , tablesWeights = stateWeights (const 1) $ tablesTokens tables
            }
    stateClasses =
        fromRight (error "prefixCompletions: an automaton without a guard has size classes") $
            sizedStates automaton

{- | The completions of the empty prefix of an automaton with guards, which the
solver decides on each term. The candidates are the terms that the automaton
accepts with each constraint reduced to its equality constraints: an
over-approximation, which the solver checks again on every candidate. A
candidate that the solver rejects ('No') goes. The others stay, as accepted
('Yes') or as undecided ('Unknown').

The verdict of a term is 'Yes' when the guards of some run all hold, 'No' when
each run has a guard that fails, and 'Unknown' otherwise, in the three-valued
logic of 'andVerdicts' and 'orVerdicts'. A guard of a run is decided even when
another guard of the run is 'Unknown', so this verdict is 'No' in some cases
where 'Data.CFTA.Refinement.Denotation.accepts' is 'Unknown'. The two agree
on 'Yes'. The verdict of each state on each subterm is kept, and so is the
verdict of each constraint of a transition on the subterms at the paths that
it reads, so the solver decides each such question once.

An automaton without a guard beyond equality constraints gives the result of
'prefixCompletions', and the solver is not called.
-}
prefixCompletionsWith ::
    (Ord state) => Entailment -> Size -> FTA.FTA state Symbol Constraint -> IO (Completions Symbol)
prefixCompletionsWith entailment size automaton = case prefixCompletions size automaton of
    Right completions -> pure completions
    Left _ -> decided =<< deciding entailment size automaton

{- | The completions of a prefix of an automaton with guards, whose verdicts the
solver decides when a query needs them. The candidates and their verdicts are
those of 'prefixCompletionsWith'. Each value of a walk shares the memories of
the verdicts: the verdict of each state on each subterm, and the verdict of
each constraint of a transition on the subterms at the paths that it reads.
So in the whole walk, the solver decides each constraint of a transition at
most once for each value of the subterms that it reads.
-}
data Deciding = Deciding
    { decidingTokensBefore :: [(Symbol, Int)]
    -- ^ The prefix, the last token first.
    , decidingBudget :: !Integer
    -- ^ The number of nodes that the pending nodes can have together.
    , decidingCandidates :: [(Term Symbol, [(Symbol, Int)])]
    -- ^ The candidates that start with the prefix, in order, each with its tokens after the prefix.
    , decidingPending :: [Path]
    -- ^ The paths of the pending nodes from the root, in preorder.
    , decidingRuns :: Set.Set Run
    -- ^ The runs on the prefix that can have a candidate within the budget.
    , decidingMachine :: Machine
    , decidingCap :: Int
    -- ^ The number of fillings that a query tries before the product, with equality constraints.
    , decidingFellBack :: IORef Bool
    -- ^ Whether a query of the walk has used the product: then the later queries use it at once.
    , decidingProduct :: Maybe (Node Symbol)
    {- ^ With equality constraints, the automaton of the terms of each exact
    size up to the bound, restricted to the prefix: its enumeration gives the
    completions, with the equalities solved by unification.
    -}
    }

-- \^ The automaton, and the memories of the verdicts, for the whole walk.

{- | A run of the automaton on the nodes of a prefix: the stack of pending
states; the constraints of the prefix nodes that the prefix does not decide,
each as the path of its node, its state, and the index of its transition; and
whether a constraint that the prefix decides is 'Unknown'.
-}
type Run = ([Int], [(Path, Int, Int)], Bool)

-- | The automaton of a walk, with each state as its number, and its verdicts.
data Machine = Machine
    { machineTokens :: IntMap.IntMap (Map.Map (Symbol, Int) [([Int], Int)])
    -- ^ The transitions of each state by token: their child states and their index.
    , machineConstraints :: IntMap.IntMap (IntMap.IntMap Constraint)
    -- ^ The constraint of each transition of each state, by index.
    , machineMinimum :: IntMap.IntMap Integer
    -- ^ The least size of a term of each state that accepts a term, without the constraints.
    , machineClasses :: Int -> Sized Symbol
    -- ^ The size classes of each state, with each constraint reduced to its equality constraints.
    , machineState :: Int -> Term Symbol -> IO Verdict
    -- ^ The verdict of a state on a term, kept for the whole walk.
    , machineConstraint :: Int -> Int -> Term Symbol -> IO Verdict
    -- ^ The verdict of the constraint of a transition on a term, kept for the whole walk.
    , machineInitial :: Int
    -- ^ The initial state.
    }

{- | The walk of the empty prefix of an automaton with guards. No guard is
decided yet.
-}
deciding :: (Ord state) => Entailment -> Size -> FTA.FTA state Symbol Constraint -> IO Deciding
deciding = decidingWithCap fillingsBeforeProduct

{- | The number of fillings of the pending states that a query of a walk tries
for a token, with equality constraints, before it builds the product by size
('decidingWithCap'). The fillings ignore the equality classes that join two
pending nodes, so a query can need very many of them; the product solves
those classes by unification, but its construction costs more than a few
fillings. After the first query that uses the product, the later queries of
the walk use it at once.

On the probe of the walk, the queries of the typed arithmetic with three
children needed at most 160 fillings up to 21 nodes, and a few queries of the
sums and the pairs needed thousands. So the queries of the arithmetic stay in
the fillings, and those of the sums and the pairs pay 256 fillings once.
-}
fillingsBeforeProduct :: Int
fillingsBeforeProduct = 256

{- | 'deciding' with the number of fillings that a query tries before the
product by size. With 0, every query of an automaton with equality
constraints enumerates the product. Both routes give the same verdicts.
-}
decidingWithCap :: (Ord state) => Int -> Entailment -> Size -> FTA.FTA state Symbol Constraint -> IO Deciding
decidingWithCap cap entailment (Size bound) automaton = do
    fellBack <- newIORef False
    (stateVerdict, constraintVerdict) <- memoryOfVerdicts entailment numberedRows
    let machine =
            Machine
                { machineTokens =
                    IntMap.map
                        ( \row ->
                            Map.fromListWith
                                (flip (<>))
                                [(tokenOf transition, [(FTA.transitionChildren transition, index)]) | (index, transition) <- row]
                        )
                        numberedRows
                , machineConstraints =
                    IntMap.map
                        (\row -> IntMap.fromList [(index, FTA.transitionConstraint transition) | (index, transition) <- row])
                        numberedRows
                , machineMinimum = IntMap.fromList [(number state, size) | (state, Size size) <- Map.toList $ Ordinary.minimumSizes rows]
                , machineClasses = (reducedClasses Map.!) . (states IntMap.!)
                , machineState = stateVerdict
                , machineConstraint = constraintVerdict
                , machineInitial = number $ FTA.initialState automaton
                }
    pure
        Deciding
            { decidingTokensBefore = []
            , decidingBudget = bound
            , decidingCandidates =
                [(term, preorder term) | size <- [1 .. bound], term <- termsOfSize (reduced $ FTA.initialState automaton) (Size size)]
            , decidingPending = [path []]
            , decidingRuns = Set.fromList $ filter (runFits machine bound) [([machineInitial machine], [], False)]
            , decidingMachine = machine
            , decidingCap = cap
            , decidingFellBack = fellBack
            , decidingProduct =
                if any (any (hasEqualities . FTA.transitionConstraint)) (FTA.transitionTable $ FTA.trim automaton)
                    then Just $ fromFTA $ FTA.trim $ bySize bound automaton
                    else Nothing
            }
  where
    rows = FTA.transitionTable automaton
    numbers = Map.fromList $ zip (Map.keys rows) [0 :: Int ..]
    number state = numbers Map.! state
    states = IntMap.fromList [(index, state) | (state, index) <- Map.toList numbers]
    numberedRows =
        IntMap.fromList
            [ ( number state
              , zip
                    [0 ..]
                    [transition{FTA.transitionChildren = map number $ FTA.transitionChildren transition} | transition <- transitions]
              )
            | (state, transitions) <- Map.toList rows
            ]
    tokenOf transition = (FTA.transitionSymbol transition, length $ FTA.transitionChildren transition)
    reduced =
        fromRight (error "deciding: an automaton with equality constraints has size classes")
            $ sizedStates
            $ FTA.mapConstraints (equalityConstraint . equalities) automaton
    reducedClasses = Map.fromList [(state, reduced state) | state <- Map.keys rows]

-- | The completions of the empty prefix, with the weight one for each symbol.
emptyPrefix :: Integer -> Route symbol -> Completions symbol
emptyPrefix bound = Completions [] bound (const 1)

-- | The prefix of a walk, the first token first.
decidingPrefix :: Deciding -> [(Symbol, Int)]
decidingPrefix = reverse . decidingTokensBefore

{- | The walk after one more token. 'Nothing' when the solver rejects every
candidate that starts with the prefix and the token, as 'afterToken' gives.
The solver decides the candidates of the runs after the token, smallest
first, until one is not rejected.
-}
decidingStep :: Deciding -> (Symbol, Int) -> IO (Maybe Deciding)
decidingStep walk token = do
    (runs, verdicts, restricted) <- afterRuns walk token
    found <- anyIO (fmap (/= No)) $ verdicts $ Set.toList runs
    pure $
        if found
            then
                Just
                    walk
                        { decidingTokensBefore = token : decidingTokensBefore walk
                        , decidingBudget = decidingBudget walk - 1
                        , decidingCandidates = [(term, rest) | (term, next : rest) <- decidingCandidates walk, next == token]
                        , decidingPending = pendingAfter walk token
                        , decidingRuns = runs
                        , decidingProduct = restricted
                        }
            else Nothing

{- | The verdict of the prefix as a term ('completeVerdict'), and the verdict of
each next token in ascending order: 'Yes' for a token of 'nextTokens',
'Unknown' for a token of 'undecidedTokens'. A rejected token is not in the
list.

The next tokens come from the runs of the automaton on the prefix, not from
the candidates. After a token, a constraint of a prefix node whose paths the
prefix fixes is decided once for all the candidates of the run: a run whose
constraint fails goes, and a run whose constraint is 'Unknown' has no
accepted candidate. Then the solver decides the candidates of the runs,
smallest first, until one is accepted; for an undecided token, until one is
not rejected. So a token needs every candidate of a run decided only when no
candidate of the run is accepted and the prefix does not decide that.
-}
decidingTokens :: Deciding -> IO (Verdict, [((Symbol, Int), Verdict)])
decidingTokens walk = do
    tokens <- traverse (\token -> (,) token <$> tokenVerdict token) candidates
    pure (complete, [(token, verdict) | (token, verdict) <- tokens, verdict /= No])
  where
    runs = Set.toList $ decidingRuns walk
    complete = case [unknown | ([], _, unknown) <- runs] of
        [] -> No
        flags -> if and flags then Unknown else Yes
    candidates =
        Set.toList $
            Set.fromList
                [ token
                | (top : _, _, _) <- runs
                , token <- Map.keys $ IntMap.findWithDefault Map.empty top $ machineTokens $ decidingMachine walk
                ]
    tokenVerdict token = do
        (after, verdicts, _) <- afterRuns walk token
        best <- firstAccepted No $ verdicts [run | run@(_, _, False) <- Set.toList after]
        case best of
            No -> do
                undecided <- anyIO (fmap (/= No)) $ verdicts [run | run@(_, _, True) <- Set.toList after]
                pure $ if undecided then Unknown else No
            _ -> pure best
    -- 'Yes' at the first accepted candidate, else whether one was undecided.
    firstAccepted found [] = pure found
    firstAccepted found (decide : rest) = do
        verdict <- decide
        case verdict of
            Yes -> pure Yes
            Unknown -> firstAccepted Unknown rest
            No -> firstAccepted found rest

{- | The runs after a token, with the constraints that the prefix and the token
decide; the verdicts of the candidates of given runs, smallest first; and,
with equality constraints, the product restricted to the prefix and the token.

Without equality constraints, the candidates of a run are the fillings of its
pending states. With them, a filling can break an equality class that joins
two pending nodes, and the search would try fillings until one holds. So
after the cap of fillings, the candidates are the terms of the product,
which the enumerator builds with the equalities solved: the first one is a
completion, and none means that there is none.
-}
afterRuns :: Deciding -> (Symbol, Int) -> IO (Set.Set Run, [Run] -> [IO Verdict], Maybe (Node Symbol))
afterRuns walk token = case decidingPending walk of
    [] -> pure (Set.empty, const [], Nothing)
    here : _ -> do
        fellBack <- readIORef $ decidingFellBack walk
        let cap = if fellBack then 0 else decidingCap walk
        found <-
            traverse
                decideRun
                [ (children <> rest, obligations <> [(here, top, index) | constraintAt top index /= noConstraint], unknown)
                | (top : rest, obligations, unknown) <- Set.toList $ decidingRuns walk
                , (children, index) <- Map.findWithDefault [] token $ IntMap.findWithDefault Map.empty top $ machineTokens machine
                , runFits machine budget (children <> rest, [], False)
                ]
        pure (Set.fromList (catMaybes found), verdictsOf cap, restricted)
  where
    restricted = case decidingPending walk of
        here : _ -> restrictAt (unPath here) (TemplateNode (fst token) (replicate (snd token) Hole)) <$> decidingProduct walk
        [] -> Nothing
    machine = decidingMachine walk
    budget = decidingBudget walk - 1
    prefix = decidingPrefix walk <> [token]
    pending = pendingAfter walk token
    template = preorderPrefix prefix
    -- The prefix with a leaf at each pending node: the constraints that the
    -- prefix decides do not read the pending nodes.
    placeholder = fill prefix [Term.Node (fst token) [] | _ <- pending]
    constraintAt state index = IntMap.findWithDefault IntMap.empty state (machineConstraints machine) IntMap.! index
    decideRun (stack, obligations, unknown) = go [] unknown obligations
      where
        go open flag [] = pure $ Just (stack, reverse open, flag)
        go open flag (obligation@(node, state, index) : rest)
            | equalitiesFail template node (constraintAt state index) = pure Nothing
            | decidedBy template node (constraintAt state index) = do
                verdict <- case getPath node placeholder of
                    Just subterm -> machineConstraint machine state index subterm
                    Nothing -> pure No
                case verdict of
                    No -> pure Nothing
                    Yes -> go open flag rest
                    Unknown -> go open True rest
            | otherwise = go (obligation : open) flag rest
    -- The verdicts of the candidates of the runs: the fillings, smallest
    -- first; with equality constraints, after the cap, the terms of the product.
    verdictsOf _ [] = []
    verdictsOf cap runs = case restricted of
        Just node -> capped cap node (fillingVerdicts runs)
        Nothing -> fillingVerdicts runs
    -- The first fillings up to the cap, then the terms of the product if a
    -- filling remains. The list is lazy, so a query that ends in the
    -- fillings builds no product. The product notes that the walk uses it,
    -- with a verdict 'No' that changes no answer.
    capped _ _ [] = []
    capped 0 node _ =
        (writeIORef (decidingFellBack walk) True >> pure No)
            : map (machineState machine $ machineInitial machine) (Enumeration.terms node)
    capped left node (verdict : rest) = verdict : capped (left - 1) node rest
    fillingVerdicts runs =
        [ candidateVerdict run terms
        | size <- [0 .. budget]
        , run@(stack, _, _) <- runs
        , terms <- fillings (machineClasses machine) stack size
        ]
    candidateVerdict (stack, open, flag) terms =
        andVerdicts $
            [pure Unknown | flag]
                <> [ maybe (pure No) (machineConstraint machine state index) (getPath node term)
                   | let term = fill prefix terms
                   , (node, state, index) <- open
                   ]
                <> zipWith (machineState machine) stack terms

-- | Whether a constraint has an equality class.
hasEqualities :: Constraint -> Bool
hasEqualities constraint = case equalities constraint of
    EqConstraints [] -> False
    _ -> True

{- | The automaton of the terms with at most the given number of nodes: a state
for each state and exact size, and a root for every size. A transition has a
copy for each split of its size over its children. Children that one class of
its equality constraints names directly have one size, because equal terms
have equal sizes. The constraints keep their paths. The automaton is acyclic,
so its enumeration ends, and it has no term above the bound.

A transition with @k@ children has a copy for each of the about
@size^(k-1)@ splits of each size, so the automaton grows with the arities.
-}
bySize ::
    (Ord state) =>
    Integer -> FTA.FTA state symbol Constraint -> FTA.FTA (Maybe (state, Integer)) symbol Constraint
bySize bound automaton =
    fromRight (error "bySize: the states of a valid automaton give a valid automaton")
        $ FTA.mkFTA Nothing
        $ (Nothing, root)
            : explore Set.empty [child | transition <- root, Just child <- FTA.transitionChildren transition] []
  where
    initial = FTA.initialState automaton
    least = Map.map (\(Size size) -> size) $ Ordinary.minimumSizes $ FTA.transitionTable automaton
    root = concat [rowOf initial size | size <- [1 .. bound]]
    -- The rows of the pairs of a state and a size that the root reaches.
    explore _ [] rows = rows
    explore seen (pair@(state, size) : pending) rows
        | Set.member pair seen = explore seen pending rows
        | otherwise =
            let row = rowOf state size
             in explore
                    (Set.insert pair seen)
                    ([child | transition <- row, Just child <- FTA.transitionChildren transition] <> pending)
                    ((Just pair, row) : rows)
    rowOf state size =
        [ transition
            { FTA.transitionChildren = zipWith (curry Just) (FTA.transitionChildren transition) parts
            }
        | transition <- FTA.transitionsFrom automaton state
        , parts <- splits (FTA.transitionChildren transition) (size - 1)
        , equalSizes (FTA.transitionConstraint transition) parts
        ]
    -- The sizes of the children, each at least the least size of its state.
    splits [] total = [[] | total == 0]
    splits (child : rest) total = case (Map.lookup child least, traverse (`Map.lookup` least) rest) of
        (Just smallest, Just others) ->
            [first : sizes | first <- [smallest .. total - sum others], sizes <- splits rest (total - first)]
        _ -> []
    equalSizes constraint parts = case equalities constraint of
        EqConstraints classes ->
            and
                [ all (== first) rest
                | equal <- classes
                , first : rest <- [[parts !! child | [ChildIndex child] <- map unPath $ Set.toList $ unPathEClass equal]]
                ]
        _ -> True

-- | A node with the node at a path below its root restricted to a template.
restrictAt :: [ChildIndex] -> Template Symbol -> Node Symbol -> Node Symbol
restrictAt [] template node = restrict template node
restrictAt (ChildIndex index : rest) template node =
    Node
        [ setChildren
            edge
            [ if position == index then restrictAt rest template child else child
            | (position, child) <- zip [0 ..] $ edgeChildren edge
            ]
        | edge <- nodeEdges node
        ]

{- | Whether the prefix decides that the equality constraints of the node at a
path fail for every completion: a path leaves the term at a node that the
prefix fixes, or two paths of a class reach nodes that the prefix fixes with
different symbols or numbers of children at the same place.
-}
equalitiesFail :: Template Symbol -> Path -> Constraint -> Bool
equalitiesFail template node constraint = case equalities constraint of
    EqConstraints classes -> any (classFails . map (at template . (unPath node <>) . unPath) . Set.toList . unPathEClass) classes
    _ -> True
  where
    classFails found =
        Nothing `elem` found || or [conflict left right | (left, rights) <- pairs (catMaybes found), right <- rights]
    pairs (first : rest) = (first, rest) : pairs rest
    pairs [] = []
    -- The part of the prefix at a path: 'Nothing' when the path leaves the
    -- term at a node that the prefix fixes, and 'Just Hole' below a pending node.
    at part [] = Just part
    at (TemplateNode _ children) (ChildIndex child : rest) = case drop child children of
        next : _ | child >= 0 -> at next rest
        _ -> Nothing
    at _ _ = Just Hole
    conflict (TemplateNode left lefts) (TemplateNode right rights) =
        left /= right || length lefts /= length rights || or (zipWith conflict lefts rights)
    conflict _ _ = False

-- | Whether the prefix fixes every path that a constraint of the node at a path reads.
decidedBy :: Template Symbol -> Path -> Constraint -> Bool
decidedBy template node constraint =
    all (fixedAt template . (unPath node <>) . unPath) $ Set.toList $ constraintPaths constraint
  where
    fixedAt Hole _ = False
    fixedAt part [] = complete part
    fixedAt (TemplateNode _ children) (ChildIndex child : rest) = case drop child children of
        next : _ | child >= 0 -> fixedAt next rest
        _ -> True
    fixedAt _ _ = False
    complete (TemplateNode _ children) = all complete children
    complete _ = False

-- | The paths of the pending nodes after a token.
pendingAfter :: Deciding -> (Symbol, Int) -> [Path]
pendingAfter walk (_, arity) = case decidingPending walk of
    [] -> []
    here : rest -> [path (unPath here <> [ChildIndex child]) | child <- [0 .. arity - 1]] <> rest

-- | Whether the pending states of a run have terms within the budget, without the constraints.
runFits :: Machine -> Integer -> Run -> Bool
runFits machine budget (stack, _, _) =
    maybe False ((<= budget) . sum) $ traverse (`IntMap.lookup` machineMinimum machine) stack

{- | The completions of the prefix of a walk, with every candidate decided: the
completions that 'prefixCompletionsWith' and 'afterPrefix' give, with the
weight one for each symbol. 'withWeights' weighs them; a weight needs every
candidate decided, as a count does.
-}
decided :: Deciding -> IO (Completions Symbol)
decided walk = do
    found <- traverse (machineState machine (machineInitial machine) . fst) $ decidingCandidates walk
    pure
        Completions
            { completionsPrefix = decidingTokensBefore walk
            , completionsBudget = decidingBudget walk
            , completionsWeight = const 1
            , completionsRoute =
                Listed [(term, rest, verdict) | ((term, rest), verdict) <- zip (decidingCandidates walk) found, verdict /= No]
            }
  where
    machine = decidingMachine walk

-- | Whether an action holds for one element, tried in order until it does.
anyIO :: (element -> IO Bool) -> [element] -> IO Bool
anyIO holds = foldr (\element rest -> holds element >>= \found -> if found then pure True else rest) (pure False)

{- | The completions after one more token. 'Nothing' when no completion
starts with the prefix and the token. With a solver, the result is 'Nothing'
only when the solver rejects every candidate; the completions after an
undecided token are all undecided.
-}
afterToken :: (Ord symbol) => Completions symbol -> (symbol, Int) -> Maybe (Completions symbol)
afterToken completions token = case completionsRoute completions of
    Stacks tables stacks ->
        let kept =
                Set.fromList
                    [ stack
                    | top : rest <- Set.toList stacks
                    , children <- Map.findWithDefault [] token $ IntMap.findWithDefault Map.empty top $ tablesTokens tables
                    , let stack = children <> rest
                    , fits tables budget stack
                    ]
         in if Set.null kept then Nothing else Just $ after $ Stacks tables kept
    Listed listed ->
        let kept = [(term, rest, verdict) | (term, next : rest, verdict) <- listed, next == token]
         in if null kept then Nothing else Just $ after $ Listed kept
  where
    budget = completionsBudget completions - 1
    after route =
        completions
            { completionsPrefix = token : completionsPrefix completions
            , completionsBudget = budget
            , completionsRoute = route
            }

{- | The completions after more tokens, the first token first. 'Nothing' when
no completion starts with the prefix and the tokens.
-}
afterPrefix :: (Ord symbol) => Completions symbol -> [(symbol, Int)] -> Maybe (Completions symbol)
afterPrefix = foldM afterToken

-- | The prefix of the completions, the first token first.
completionPrefix :: Completions symbol -> [(symbol, Int)]
completionPrefix = reverse . completionsPrefix

{- | The tokens that can come next, in ascending order, each with the number of
completions that start with the prefix and the token. A token that is not in
the list has no completion. With a solver, a token is in the list when the
solver accepts one of its completions, and the number counts the accepted
completions. The token can have undecided completions too.
-}
nextTokens :: (Ord symbol) => Completions symbol -> [((symbol, Int), Cardinality)]
nextTokens completions = case completionsRoute completions of
    Stacks tables stacks ->
        [ (token, completionCount after)
        | token <-
            Set.toList $
                Set.fromList
                    [ token
                    | top : _ <- Set.toList stacks
                    , token <- Map.keys $ IntMap.findWithDefault Map.empty top $ tablesTokens tables
                    ]
        , Just after <- [afterToken completions token]
        ]
    Listed listed -> Map.toList $ Map.fromListWith (+) [(next, 1) | (_, next : _, Yes) <- listed]

{- | The tokens that the solver neither offers nor rejects, in ascending order:
the solver accepts no completion that starts with the prefix and the token,
and it does not decide some of them. Each token has the number of its
undecided completions. A token in neither this list nor 'nextTokens' is
rejected: the solver rejects each of its completions.
-}
undecidedTokens :: (Ord symbol) => Completions symbol -> [((symbol, Int), Cardinality)]
undecidedTokens completions = case completionsRoute completions of
    Stacks _ _ -> []
    Listed listed ->
        [ (token, undecided)
        | (token, (Cardinality 0, undecided)) <-
            Map.toList $
                Map.fromListWith add [(next, if verdict == Yes then (1, 0) else (0, 1)) | (_, next : _, verdict) <- listed]
        ]
  where
    add (accepted, undecided) (accepted', undecided') = (accepted + accepted', undecided + undecided')

-- | Whether the prefix is the preorder of an accepted term within the bound.
isComplete :: Completions symbol -> Bool
isComplete = (== Yes) . completeVerdict

{- | Whether the prefix is the preorder of an accepted term within the bound:
'Yes' or 'No', or 'Unknown' when the prefix is a term that the solver does not
decide.
-}
completeVerdict :: Completions symbol -> Verdict
completeVerdict completions = case completionsRoute completions of
    Stacks _ stacks -> if Set.member [] stacks then Yes else No
    Listed listed -> case [verdict | (_, [], verdict) <- listed] of
        verdict : _ -> verdict
        [] -> No

-- | The number of completions.
completionCount :: (Ord symbol) => Completions symbol -> Cardinality
completionCount completions = case completionsRoute completions of
    Stacks tables stacks
        | tablesUnambiguous tables ->
            Cardinality $ sum [sum $ stackCounts tables (completionsBudget completions) stack | stack <- Set.toList stacks]
    _ -> Cardinality $ genericLength $ completionTerms completions

-- | The completions, each once, in order.
completionTerms :: (Ord symbol) => Completions symbol -> [Term symbol]
completionTerms completions = case completionsRoute completions of
    Stacks tables stacks
        | tablesUnambiguous tables -> listed tables stacks
        | otherwise -> nubOrd $ listed tables stacks
    Listed terms -> [term | (term, _, Yes) <- terms]
  where
    prefix = completionPrefix completions
    listed tables stacks =
        [ fill prefix terms
        | size <- [0 .. completionsBudget completions]
        , stack <- Set.toList stacks
        , terms <- fillings (classesOf tables) stack size
        ]

{- | The completions that the solver does not decide, each once, in order.
Without a solver, the list is empty.
-}
undecidedTerms :: Completions symbol -> [Term symbol]
undecidedTerms completions = case completionsRoute completions of
    Stacks _ _ -> []
    Listed terms -> [term | (term, _, Unknown) <- terms]

{- | The completion at a rank in the order of 'completionTerms'. 'Nothing'
when the rank is outside the completions. The rank is a place among the
completions of this prefix, not the rank of the term in the whole language.
-}
unrankCompletion :: (Ord symbol) => Completions symbol -> Rank -> Maybe (Term symbol)
unrankCompletion completions (Rank rank)
    | rank < 0 = Nothing
    | otherwise = case completionsRoute completions of
        Stacks tables stacks
            | tablesUnambiguous tables ->
                let counted = [(stack, stackCounts tables budget stack) | stack <- Set.toList stacks]
                    select _ [] = Nothing
                    select remaining ((stack, size, count) : rest)
                        | remaining < count = unrankFilling tables budget stack size remaining
                        | otherwise = select (remaining - count) rest
                 in fmap (fill $ completionPrefix completions) $
                        select rank [(stack, size, counts `genericIndex` size) | size <- [0 .. budget], (stack, counts) <- counted]
        _ -> listToMaybe $ genericDrop rank $ completionTerms completions
  where
    budget = completionsBudget completions

{- | A generator of the completions, each with the same probability. It draws
a rank and unranks it. 'Nothing' when there is no completion.
-}
sampleCompletion :: (Ord symbol) => Completions symbol -> Maybe (QC.Gen (Term symbol))
sampleCompletion completions
    | count <= 0 = Nothing
    | otherwise =
        Just $
            fromMaybe (error "sampleCompletion: a rank below the count has a completion")
                . unrankCompletion completions
                . Rank
                <$> QC.chooseInteger (0, count - 1)
  where
    Cardinality count = completionCount completions

-- Weights

{- | The completions with a weight for each symbol, which must not be
negative. The weight of a term is the product of the weights of the symbols
of its nodes, the nodes of the prefix included. A completion is a term, not a
run, so its weight does not depend on the run that accepts it. Without
'withWeights', each symbol has the weight one, and the weight of the
completions is their number.
-}
withWeights :: (symbol -> Rational) -> Completions symbol -> Completions symbol
withWeights weight completions =
    completions
        { completionsWeight = weight
        , completionsRoute = case completionsRoute completions of
            Stacks tables stacks -> Stacks tables{tablesWeights = stateWeights weight $ tablesTokens tables} stacks
            listed -> listed
        }

{- | The total weight of the completions. With unambiguous rows and no
constraint, it is a convolution of the weights of the pending states.
Otherwise it is the sum of the weights of the listed completions.
-}
completionWeight :: (Ord symbol) => Completions symbol -> Rational
completionWeight completions = case completionsRoute completions of
    Stacks tables stacks
        | tablesUnambiguous tables ->
            prefixWeight completions * sum [sum $ stackWeights tables budget stack | stack <- Set.toList stacks]
    _ -> sum $ map (termWeight $ completionsWeight completions) $ completionTerms completions
  where
    budget = completionsBudget completions

{- | The tokens of 'nextTokens', each with the total weight of the completions
that start with the prefix and the token. A token with completions whose
weight is zero has the weight zero.
-}
nextTokenWeights :: (Ord symbol) => Completions symbol -> [((symbol, Int), Rational)]
nextTokenWeights completions =
    [ (token, maybe 0 completionWeight $ afterToken completions token)
    | (token, _) <- nextTokens completions
    ]

{- | The probability of a token after the prefix: the weight of the completions
that continue with it, divided by the weight of the completions. The weight of
the prefix is in both, so it cancels. 'Nothing' when the completions have the
weight zero. A token without a completion has the probability zero.
-}
tokenProbability :: (Ord symbol) => Completions symbol -> (symbol, Int) -> Maybe Rational
tokenProbability completions token
    | total <= 0 = Nothing
    | otherwise = Just $ maybe 0 completionWeight (afterToken completions token) / total
  where
    total = completionWeight completions

{- | A generator of the completions, each with a probability in proportion to
its weight. 'Nothing' when the completions have the weight zero. Each choice
scales its weights to integers and draws one of them, so the probabilities
are exact.
-}
sampleWeighted :: (Ord symbol) => Completions symbol -> Maybe (QC.Gen (Term symbol))
sampleWeighted = drawCompletion chooseInteger
  where
    chooseInteger weights = do
        let scale = foldr (lcm . denominator) 1 weights
            scaled = [numerator (weight * fromInteger scale) | weight <- weights]
        drawn <- QC.chooseInteger (0, sum scaled - 1)
        pure $ length $ takeWhile (<= drawn) $ scanl1 (+) scaled

{- | A completion, drawn with a function that chooses an index of a list of
weights. 'Nothing' when the completions have the weight zero. The draw gives
each completion a probability in proportion to its weight when the function
chooses the index @i@ with the probability of the weight @i@ over the sum of
the weights, as the function of 'sampleWeighted' does.

With unambiguous rows and no constraint, the draw chooses the size and the
stack of pending states, then the size of each pending node, then the
transition of each node, each in proportion to the weights of its
completions. Otherwise it chooses one listed completion. The order of the
choices inside a size class follows the transitions, not the class ranks of
"Data.CFTA.Sized", so with the weight one for each symbol the probabilities
are uniform, but one draw can give another completion than 'sampleCompletion'.
-}
drawCompletion :: (Monad m, Ord symbol) => ([Rational] -> m Int) -> Completions symbol -> Maybe (m (Term symbol))
drawCompletion choose completions
    | completionWeight completions <= 0 = Nothing
    | otherwise = Just $ case completionsRoute completions of
        Stacks tables stacks
            | tablesUnambiguous tables -> do
                let options =
                        [ (stack, size, weights `genericIndex` size)
                        | size <- [0 .. budget]
                        , (stack, weights) <- [(stack, stackWeights tables budget stack) | stack <- Set.toList stacks]
                        ]
                index <- choose [stackWeight | (_, _, stackWeight) <- options]
                let (stack, size, _) = options !! index
                fill (completionPrefix completions) <$> drawFilling tables stack size
        _ -> do
            let terms = completionTerms completions
            index <- choose $ map (termWeight weight) terms
            pure $ terms !! index
  where
    budget = completionsBudget completions
    weight = completionsWeight completions
    -- The terms of a stack of pending states with the given total size.
    drawFilling _ [] _ = pure []
    drawFilling tables (state : rest) size = do
        let restWeights = stackWeights tables size rest
            options =
                [ (first, weightsOf tables state `genericIndex` first * restWeights `genericIndex` (size - first)) | first <- [1 .. size]
                ]
        index <- choose $ map snd options
        let first = fst $ options !! index
        (:) <$> drawTerm tables state first <*> drawFilling tables rest (size - first)
    -- A term of a state with the given size.
    drawTerm tables state size = do
        let options =
                [ (symbol, children, weight symbol * stackWeights tables (size - 1) children `genericIndex` (size - 1))
                | ((symbol, _), childLists) <- Map.toList $ IntMap.findWithDefault Map.empty state $ tablesTokens tables
                , children <- childLists
                ]
        index <- choose [optionWeight | (_, _, optionWeight) <- options]
        let (symbol, children, _) = options !! index
        Term.Node symbol <$> drawFilling tables children (size - 1)

-- | The weight of the nodes of the prefix.
prefixWeight :: Completions symbol -> Rational
prefixWeight completions = product [completionsWeight completions symbol | (symbol, _) <- completionsPrefix completions]

-- | The weight of a term: the product of the weights of its symbols.
termWeight :: (symbol -> Rational) -> Term symbol -> Rational
termWeight weight = foldr ((*) . weight) 1

{- | The total weight of the terms of each state for each size from zero: a
choice over the transitions of the state, each the weight of its symbol times
the product of the weights of its children, with one node for the
transition. The rows must be unambiguous, so that each term has one run.
-}
stateWeights :: (symbol -> Rational) -> IntMap.IntMap (Map.Map (symbol, Int) [[Int]]) -> IntMap.IntMap [Rational]
stateWeights weight tokens = table
  where
    table = IntMap.map (\byToken -> map (weightAt byToken) [0 ..]) tokens
    weightAt _ 0 = 0
    weightAt byToken size =
        sum
            [ weight symbol * childWeights (size - 1) children `genericIndex` (size - 1)
            | ((symbol, _), childLists) <- Map.toList byToken
            , children <- childLists
            ]
    -- The weights of the children of a transition, up to a total size.
    childWeights degree children =
        products degree [genericTake (degree + 1) $ IntMap.findWithDefault (repeat 0) child table | child <- children]

-- | The weights of the terms of a state, for each size from zero.
weightsOf :: Tables symbol -> Int -> [Rational]
weightsOf tables state = IntMap.findWithDefault (repeat 0) state $ tablesWeights tables

-- | The weight of the fillings of a stack of pending states, for each total size from zero to the budget.
stackWeights :: Tables symbol -> Integer -> [Int] -> [Rational]
stackWeights tables budget stack = products budget [genericTake (budget + 1) $ weightsOf tables state | state <- stack]

{- | The product of polynomials up to a degree: each polynomial is its list of
coefficients from degree zero, and the result has the coefficients from zero
to the degree.
-}
products :: (Num value) => Integer -> [[value]] -> [value]
products degree = foldr convolve (1 : genericReplicate degree 0)
  where
    convolve left right = [sum $ zipWith (*) (reverse $ genericTake (size + 1) left) right | size <- [0 .. degree]]

-- | Whether a stack of pending states has a filling within the budget.
fits :: Tables symbol -> Integer -> [Int] -> Bool
fits tables budget stack = maybe False ((<= budget) . sum) $ traverse (`IntMap.lookup` tablesMinimum tables) stack

-- | The size classes of a state.
classesOf :: Tables symbol -> Int -> Sized symbol
classesOf tables state = tablesClasses tables IntMap.! state

{- | The number of fillings of a stack of pending states, for each total size
from zero to the budget. The rows must be unambiguous.
-}
stackCounts :: Tables symbol -> Integer -> [Int] -> [Integer]
stackCounts tables budget = products budget . map stateCounts
  where
    stateCounts state =
        0 : [count | size <- [1 .. budget], let Cardinality count = countOfSize (classesOf tables state) (Size size)]

{- | The fillings of a stack of pending states with the given total size, in
order: the term of the first pending node varies slowest.
-}
fillings :: (Int -> Sized symbol) -> [Int] -> Integer -> [[Term symbol]]
fillings _ [] size = [[] | size == 0]
fillings classes (state : rest) size =
    [ term : terms
    | first <- [1 .. size]
    , term <- termsOfSize (classes state) (Size first)
    , terms <- fillings classes rest (size - first)
    ]

{- | The filling at a rank among the fillings of a stack with the given total
size, in the order of 'fillings'. The rows must be unambiguous.
-}
unrankFilling :: Tables symbol -> Integer -> [Int] -> Integer -> Integer -> Maybe [Term symbol]
unrankFilling _ _ [] _ _ = Just []
unrankFilling tables budget (state : rest) size rank = go 1 rank
  where
    classes = classesOf tables state
    restCounts = stackCounts tables budget rest
    go first remaining
        | first > size = Nothing
        | remaining < count * inner =
            let (major, minor) = remaining `quotRem` inner
             in (:)
                    <$> unrankOfSize classes (Size first) (ClassRank major)
                    <*> unrankFilling tables budget rest (size - first) minor
        | otherwise = go (first + 1) (remaining - count * inner)
      where
        Cardinality count = countOfSize classes (Size first)
        inner = restCounts `genericIndex` (size - first)

{- | The verdict of the initial state on a term, as 'prefixCompletionsWith'
defines it. Two memories last for every later call of the function: the
verdict of each state on each subterm, and the verdict of the constraint of
each transition on the subterms at the paths that it reads
('constraintPaths'). A constraint reads the term only at those paths, so two
terms with the same subterms there have the same verdict, and the solver
decides each such question once. The constraint of a transition is decided
before its children, so a constraint that fails rejects the term without the
verdicts of the children.
-}
memoryOfVerdicts ::
    Entailment ->
    IntMap.IntMap [(Int, FTA.Transition Int Symbol Constraint)] ->
    IO (Int -> Term Symbol -> IO Verdict, Int -> Int -> Term Symbol -> IO Verdict)
memoryOfVerdicts entailment rows = do
    states <- newIORef Map.empty
    constraints <- newIORef Map.empty
    let remembered memory key decide = do
            found <- Map.lookup key <$> readIORef memory
            case found of
                Just verdict -> pure verdict
                Nothing -> do
                    verdict <- decide
                    modifyIORef' memory $ Map.insert key verdict
                    pure verdict
        row state = IntMap.findWithDefault [] state rows
        constraintOf state index term =
            let constraint = maybe noConstraint FTA.transitionConstraint $ lookup index $ row state
             in remembered
                    constraints
                    (state, index, [getPath inspected term | inspected <- Set.toList $ constraintPaths constraint])
                    (evaluateConstraint entailment constraint term)
        verdictOf state term@(Term.Node symbol children) =
            remembered states (state, term) $
                orVerdicts
                    [ andVerdicts $
                        constraintOf state index term
                            : zipWith verdictOf (FTA.transitionChildren transition) children
                    | (index, transition) <- row state
                    , FTA.transitionSymbol transition == symbol
                    , length (FTA.transitionChildren transition) == length children
                    ]
    pure (verdictOf, constraintOf)

-- | The tokens of a term in preorder.
preorder :: Term symbol -> [(symbol, Int)]
preorder (Term.Node symbol children) = (symbol, length children) : concatMap preorder children

{- | The term whose preorder starts with a prefix and whose pending nodes hold
the given terms, in preorder.
-}
fill :: [(symbol, Int)] -> [Term symbol] -> Term symbol
fill prefix terms = case node prefix terms of
    (term, _, _) -> term
  where
    node ((symbol, count) : tokens) rest =
        let (children, tokens', rest') = nodes count tokens rest
         in (Term.Node symbol children, tokens', rest')
    node [] (term : rest) = (term, [], rest)
    node [] [] = error "fill: fewer terms than pending nodes"
    nodes 0 tokens rest = ([], tokens, rest)
    nodes count tokens rest =
        let (child, tokens', rest') = node tokens rest
            (children, tokens'', rest'') = nodes (count - 1) tokens' rest'
         in (child : children, tokens'', rest'')
