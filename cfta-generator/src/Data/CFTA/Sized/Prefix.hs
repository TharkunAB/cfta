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
convolution of the counts of its states. The counts of a state come from
'Data.CFTA.Sized.sized', with the state as the initial state. When the rows are ambiguous, one
term can complete two stacks. Then the queries list the completions and keep
the first place of each term, as 'Data.CFTA.Sized.sizedReference' does. This
is exact, but it is slow for many completions.

The completions are in order of their size, then of their stack, then of the
terms that fill the stack. The term of the first pending node varies
slowest. Each pending node goes through its sizes in ascending order, and
through each size class in the order of "Data.CFTA.Sized". For the empty
prefix, this is the order of 'Data.CFTA.Sized.sized'. The stacks are in
lexicographic order of their states, and the states are in the order of
their 'Ord' instance.

The automaton must have no constraint: an equality constraint or a guard is
not checked here, so 'prefixCompletions' rejects it.
-}
module Data.CFTA.Sized.Prefix (
    Completions,
    CompletionsError (..),
    prefixCompletions,
    afterToken,
    afterPrefix,
    completionPrefix,
    nextTokens,
    isComplete,
    completionCount,
    completionTerms,
    unrankCompletion,
    sampleCompletion,
) where

import Control.Monad (foldM, void)
import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import qualified Data.IntMap.Lazy as IntMap
import Data.List (genericDrop, genericIndex, genericLength, genericReplicate, genericTake)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, listToMaybe)
import qualified Data.Set as Set
import qualified Test.QuickCheck as QC

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import qualified Data.CFTA.Gen.Internal.Table as Ordinary
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Rank (..), Size (..))
import Data.CFTA.Sized (Sized, countOfSize, sized, termsOfSize, unrankOfSize)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | The completions of a prefix within a size bound.
data Completions symbol = Completions
    { completionsTables :: Tables symbol
    , completionsPrefix :: [(symbol, Int)]
    -- ^ The prefix, the last token first.
    , completionsBudget :: !Integer
    -- ^ The number of nodes that the pending nodes can have together.
    , completionsStacks :: !(Set.Set [Int])
    -- ^ The stacks of pending states that have a completion within the budget.
    }

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
    = -- | A transition that the initial state reaches has a constraint.
      ConstrainedTransition
    deriving (Eq, Show)

{- | The completions of the empty prefix: the terms that the automaton accepts
with at most the given number of nodes.

The result is 'ConstrainedTransition' when a transition that the initial state
reaches has a constraint other than 'noConstraint'.
-}
prefixCompletions ::
    (Ord state, Ord symbol) => Size -> FTA.FTA state symbol Constraint -> Either CompletionsError (Completions symbol)
prefixCompletions (Size bound) automaton
    | any (any ((/= noConstraint) . FTA.transitionConstraint)) (FTA.transitionTable $ FTA.trim automaton) =
        Left ConstrainedTransition
    | otherwise =
        Right
            Completions
                { completionsTables = tables
                , completionsPrefix = []
                , completionsBudget = bound
                , completionsStacks = Set.fromList $ filter (fits tables bound) [[number $ FTA.initialState automaton]]
                }
  where
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
    stateClasses state =
        fromRight (error "prefixCompletions: an automaton without constraints has size classes")
            $ sized
            $ fromRight (error "prefixCompletions: each state of a valid automaton is a valid initial state")
            $ FTA.mkFTA state (Map.toList rows)

{- | The completions after one more token. 'Nothing' when no completion
starts with the prefix and the token.
-}
afterToken :: (Ord symbol) => Completions symbol -> (symbol, Int) -> Maybe (Completions symbol)
afterToken completions token
    | Set.null stacks = Nothing
    | otherwise =
        Just
            completions
                { completionsPrefix = token : completionsPrefix completions
                , completionsBudget = budget
                , completionsStacks = stacks
                }
  where
    tables = completionsTables completions
    budget = completionsBudget completions - 1
    stacks =
        Set.fromList
            [ stack
            | top : rest <- Set.toList $ completionsStacks completions
            , children <- Map.findWithDefault [] token $ IntMap.findWithDefault Map.empty top $ tablesTokens tables
            , let stack = children <> rest
            , fits tables budget stack
            ]

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
the list has no completion.
-}
nextTokens :: (Ord symbol) => Completions symbol -> [((symbol, Int), Cardinality)]
nextTokens completions =
    [ (token, completionCount after)
    | token <- Set.toList candidates
    , Just after <- [afterToken completions token]
    ]
  where
    tokens = tablesTokens $ completionsTables completions
    candidates =
        Set.fromList
            [ token
            | top : _ <- Set.toList $ completionsStacks completions
            , token <- Map.keys $ IntMap.findWithDefault Map.empty top tokens
            ]

-- | Whether the prefix is the preorder of an accepted term within the bound.
isComplete :: Completions symbol -> Bool
isComplete = Set.member [] . completionsStacks

-- | The number of completions.
completionCount :: (Ord symbol) => Completions symbol -> Cardinality
completionCount completions
    | tablesUnambiguous tables =
        Cardinality $ sum [sum $ stackCounts tables budget stack | stack <- Set.toList $ completionsStacks completions]
    | otherwise = Cardinality $ genericLength $ completionTerms completions
  where
    tables = completionsTables completions
    budget = completionsBudget completions

-- | The completions, each once, in order.
completionTerms :: (Ord symbol) => Completions symbol -> [Term symbol]
completionTerms completions
    | tablesUnambiguous tables = listed
    | otherwise = nubOrd listed
  where
    tables = completionsTables completions
    prefix = completionPrefix completions
    listed =
        [ fill prefix terms
        | size <- [0 .. completionsBudget completions]
        , stack <- Set.toList $ completionsStacks completions
        , terms <- fillings tables stack size
        ]

{- | The completion at a rank in the order of 'completionTerms'. 'Nothing'
when the rank is outside the completions.
-}
unrankCompletion :: (Ord symbol) => Completions symbol -> Rank -> Maybe (Term symbol)
unrankCompletion completions (Rank rank)
    | rank < 0 = Nothing
    | tablesUnambiguous tables =
        fmap (fill $ completionPrefix completions) $
            select rank [(stack, size, counts `genericIndex` size) | size <- [0 .. budget], (stack, counts) <- counted]
    | otherwise = listToMaybe $ genericDrop rank $ completionTerms completions
  where
    tables = completionsTables completions
    budget = completionsBudget completions
    counted = [(stack, stackCounts tables budget stack) | stack <- Set.toList $ completionsStacks completions]
    select _ [] = Nothing
    select remaining ((stack, size, count) : rest)
        | remaining < count = unrankFilling tables budget stack size remaining
        | otherwise = select (remaining - count) rest

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
