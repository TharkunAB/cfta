{- | Weights that read the context of a node: its nearest ancestors, each with
the position of the path, and the root token of its left sibling.

'withParents' labels each symbol of an automaton with the token of its node
(the symbol and its number of children) and the context of the node. With
one ancestor and no sibling, this is the parent annotation of Johnson, /PCFG
Models of Linguistic Tree Representations/, Computational Linguistics 1998.
A state of the labelled automaton is a state of the automaton and the context
of its node. With 'reachLeftSibling', a node with a right sibling goes to a
copy of its state that accepts only the terms with one root token, so the
next sibling knows that token. The labelled automaton accepts the labelled
terms of the automaton, and each term has one labelling ('labelParents'), so
the completions of the labelled automaton are those of the automaton, size
for size. A weight of a labelled symbol ('Data.CFTA.Sized.Prefix.withWeights')
is then a weight of a token in a context, and the weighted counts, draws, and
weighted ranks of "Data.CFTA.Sized.Prefix" read the context with no other
change.

The root of a term has a context too: 'rootContext' for a term that is not
the child of a node, or the ancestors and the left sibling of a position
outside the term, as for a hole in an expression.
-}
module Data.CFTA.Sized.Prefix.Parents (
    Reach (..),
    Context (..),
    Parented,
    rootContext,
    withParents,
    labelParents,
    unlabelParents,
    labelPrefix,
) where

import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import qualified Data.Set as Set

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Sized.Prefix (Token)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | What the context of a node holds.
data Reach = Reach
    { reachAncestors :: Int
    -- ^ The number of the nearest ancestors.
    , reachLeftSibling :: Bool
    -- ^ Whether the root token of the left sibling.
    }
    deriving (Eq, Show)

-- | The context of a node.
data Context symbol = Context
    { contextAncestors :: [(Token symbol, Int)]
    -- ^ The nearest ancestors, nearest first, each the token of the ancestor and the position of the path.
    , contextLeftSibling :: Maybe (Token symbol)
    -- ^ The root token of the left sibling.
    }
    deriving (Eq, Ord, Show)

-- | The token of a node with the context of the node.
type Parented symbol = (Token symbol, Context symbol)

-- | The context of a term that is not the child of a node: no ancestor and no sibling.
rootContext :: Context symbol
rootContext = Context [] Nothing

{- | The labelled automaton of a reach, with the context of the root. Its
states are the states that the initial state reaches. 'Nothing' when a
transition has a constraint: an equality constraint compares the subterms at
two positions, and their labelled subterms have different contexts.
-}
withParents ::
    (Ord state, Ord symbol) =>
    Reach ->
    Context symbol ->
    FTA.FTA state symbol Constraint ->
    Maybe (FTA.FTA (state, Context symbol, Maybe (Token symbol)) (Parented symbol) Constraint)
withParents reach root automaton
    | any (any ((/= noConstraint) . FTA.transitionConstraint)) (FTA.transitionTable automaton) = Nothing
    | otherwise =
        Just
            $ fromRight (error "withParents: the states of a valid automaton give a valid automaton")
            $ FTA.mkFTA start
            $ explore Set.empty [start] []
  where
    start = (FTA.initialState automaton, within reach root, Nothing)
    tokens state = nubOrd [tokenOf transition | transition <- FTA.transitionsFrom automaton state]
    -- A state with a root token accepts only the terms with that root token.
    rowOf (state, context, only) =
        [ FTA.Transition (token, context) children noConstraint
        | transition <- FTA.transitionsFrom automaton state
        , let token = tokenOf transition
        , all (== token) only
        , children <- childStates token context Nothing (zip [0 ..] $ FTA.transitionChildren transition)
        ]
    -- The states of the children of a node, for each choice of the root
    -- tokens of the children that have a right sibling.
    childStates _ _ _ [] = [[]]
    childStates token context left ((position, child) : rest)
        | reachLeftSibling reach && not (null rest) =
            [(child, inner, Just first) : more | first <- tokens child, more <- childStates token context (Just first) rest]
        | otherwise = [(child, inner, Nothing) : more | more <- childStates token context Nothing rest]
      where
        inner = childContext reach token context position left
    explore _ [] rows = rows
    explore seen (state : pending) rows
        | Set.member state seen = explore seen pending rows
        | otherwise =
            let row = rowOf state
             in explore (Set.insert state seen) (concatMap FTA.transitionChildren row <> pending) ((state, row) : rows)

-- | The labelling of a term in the labelled automaton of a reach, with the context of the root.
labelParents :: Reach -> Context symbol -> Term symbol -> Term (Parented symbol)
labelParents reach root = go (within reach root)
  where
    go context node@(Term.Node _ children) =
        Term.Node
            (tokenAt node, context)
            [ go (childContext reach (tokenAt node) context position left) child
            | (position, left, child) <- zip3 [0 ..] (Nothing : map (Just . tokenAt) children) children
            ]
    tokenAt (Term.Node symbol children) = (symbol, length children)

-- | The term of a labelled term.
unlabelParents :: Term (Parented symbol) -> Term symbol
unlabelParents = fmap (fst . fst)

{- | The labelling of a prefix of tokens in preorder in the labelled automaton
of a reach, with the context of the root. 'Nothing' when a token comes after
a complete term.
-}
labelPrefix :: Reach -> Context symbol -> [Token symbol] -> Maybe [Token (Parented symbol)]
labelPrefix reach root = go [[within reach root]]
  where
    -- A stack of the contexts of the nodes still to come, one list for the
    -- children of each node. The next sibling of a node gets the root token
    -- of the node when the node starts.
    go _ [] = Just []
    go [] _ = Nothing
    go ([] : pending) tokens = go pending tokens
    go ((context : siblings) : pending) (token@(_, count) : rest) =
        (((token, context), count) :) <$> go (children : next siblings : pending) rest
      where
        children = [childContext reach token context position Nothing | position <- [0 .. count - 1]]
        next (sibling : others) = within reach sibling{contextLeftSibling = Just token} : others
        next [] = []

-- | The context of the child of a node at a position, with the root token of its left sibling.
childContext :: Reach -> Token symbol -> Context symbol -> Int -> Maybe (Token symbol) -> Context symbol
childContext reach token context position left = within reach $ Context ((token, position) : contextAncestors context) left

-- | A context with at most the ancestors and the sibling of a reach.
within :: Reach -> Context symbol -> Context symbol
within reach (Context ancestors left) =
    Context (take (reachAncestors reach) ancestors) (if reachLeftSibling reach then left else Nothing)

-- | The token of a transition.
tokenOf :: FTA.Transition state symbol constraint -> Token symbol
tokenOf transition = (FTA.transitionSymbol transition, length $ FTA.transitionChildren transition)
