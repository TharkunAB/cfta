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
) where

import Control.Monad (foldM, void)
import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import Data.IORef (modifyIORef', newIORef, readIORef)
import qualified Data.IntMap.Lazy as IntMap
import Data.List (genericDrop, genericIndex, genericLength, genericReplicate, genericTake)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, listToMaybe)
import qualified Data.Set as Set
import qualified Test.QuickCheck as QC

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalities, equalityConstraint, noConstraint, residual)
import qualified Data.CFTA.Gen.Internal.Table as Ordinary
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Rank (..), Size (..))
import Data.CFTA.Refinement.Evaluate (evaluateConstraint)
import Data.CFTA.Refinement.Verdict (Entailment, Verdict (..), andVerdicts, orVerdicts)
import Data.CFTA.Sized (Sized, countOfSize, sized, sizedStates, termsOfSize, unrankOfSize)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | The completions of a prefix within a size bound.
data Completions symbol = Completions
    { completionsPrefix :: [(symbol, Int)]
    -- ^ The prefix, the last token first.
    , completionsBudget :: !Integer
    -- ^ The number of nodes that the pending nodes can have together.
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
        Right $ Completions [] bound $ Stacks tables $ Set.fromList $ filter (fits tables bound) [[number initial]]
    | otherwise =
        Right
            $ Completions [] bound
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
on 'Yes'. The verdict of each state on each subterm is kept, so the solver
decides the guards of a state at most once on each subterm. A subterm that
two states reach is decided for each of them.

An automaton without a guard beyond equality constraints gives the result of
'prefixCompletions', and the solver is not called.
-}
prefixCompletionsWith ::
    (Ord state) => Entailment -> Size -> FTA.FTA state Symbol Constraint -> IO (Completions Symbol)
prefixCompletionsWith entailment (Size bound) automaton = case prefixCompletions (Size bound) automaton of
    Right completions -> pure completions
    Left _ -> do
        found <- termVerdicts entailment automaton candidates
        pure
            $ Completions [] bound
            $ Listed [(term, preorder term, verdict) | (term, verdict) <- zip candidates found, verdict /= No]
  where
    candidates = [term | size <- [1 .. bound], term <- termsOfSize equalitiesOnly (Size size)]
    equalitiesOnly =
        fromRight (error "prefixCompletionsWith: an automaton with equality constraints has size classes")
            $ sized
            $ FTA.mapConstraints (equalityConstraint . equalities) automaton

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
    after = Completions (token : completionsPrefix completions) budget

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
        , terms <- fillings tables stack size
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
stackCounts tables budget = foldr (convolve . stateCounts) (1 : genericReplicate budget 0)
  where
    stateCounts state =
        0 : [count | size <- [1 .. budget], let Cardinality count = countOfSize (classesOf tables state) (Size size)]
    convolve left right = [sum $ zipWith (*) (reverse $ genericTake (size + 1) left) right | size <- [0 .. budget]]

{- | The fillings of a stack of pending states with the given total size, in
order: the term of the first pending node varies slowest.
-}
fillings :: Tables symbol -> [Int] -> Integer -> [[Term symbol]]
fillings _ [] size = [[] | size == 0]
fillings tables (state : rest) size =
    [ term : terms
    | first <- [1 .. size]
    , term <- termsOfSize (classesOf tables state) (Size first)
    , terms <- fillings tables rest (size - first)
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

{- | The verdict of the initial state on each term, as 'prefixCompletionsWith'
defines it. The verdict of each state on each subterm is kept.
-}
termVerdicts :: (Ord state) => Entailment -> FTA.FTA state Symbol Constraint -> [Term Symbol] -> IO [Verdict]
termVerdicts entailment automaton terms = do
    known <- newIORef Map.empty
    let verdictOf state term@(Term.Node symbol children) = do
            found <- Map.lookup (state, term) <$> readIORef known
            case found of
                Just verdict -> pure verdict
                Nothing -> do
                    verdict <-
                        orVerdicts
                            [ andVerdicts $
                                zipWith verdictOf (FTA.transitionChildren transition) children
                                    <> [evaluateConstraint entailment (FTA.transitionConstraint transition) term]
                            | transition <- FTA.transitionsFrom automaton state
                            , FTA.transitionSymbol transition == symbol
                            , length (FTA.transitionChildren transition) == length children
                            ]
                    modifyIORef' known $ Map.insert (state, term) verdict
                    pure verdict
    traverse (verdictOf $ FTA.initialState automaton) terms

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
