{- | Weights that read the context of a node: the token of its parent and its
position among the children of the parent.

'withParents' labels each symbol of an automaton with the token of its node
(the symbol and its number of children) and the context of the node (the
parent annotation of Johnson, /PCFG Models of Linguistic Tree
Representations/, Computational Linguistics 1998). A state of the labelled
automaton is a state of the automaton and the context of its node. The
labelled automaton accepts the labelled terms of the automaton, and each
term has one labelling ('labelParents'), so the completions of the labelled
automaton are those of the automaton, size for size. A weight of a labelled
symbol ('Data.CFTA.Sized.Prefix.withWeights') is then a weight of a token in
a context, and the weighted counts, draws, and weighted ranks of
"Data.CFTA.Sized.Prefix" read the context with no other change.

The root of a term has a context too: 'Nothing' for a term that is not the
child of a node, or the token and the position of a parent outside the term,
as for a hole in an expression.
-}
module Data.CFTA.Sized.Prefix.Parents (
    Context,
    Parented,
    withParents,
    labelParents,
    unlabelParents,
    labelPrefix,
) where

import Data.Either (fromRight)
import qualified Data.Set as Set

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Sized.Prefix (Token)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | The context of a node: the token of its parent and its position, or 'Nothing' at the root.
type Context symbol = Maybe (Token symbol, Int)

-- | The token of a node with the context of the node.
type Parented symbol = (Token symbol, Context symbol)

{- | The labelled automaton, with the context of the root. Its states are the
states that the initial state reaches. 'Nothing' when a transition has a
constraint: an equality constraint compares the subterms at two positions,
and their labelled subterms have different contexts.
-}
withParents ::
    (Ord state, Ord symbol) =>
    Context symbol ->
    FTA.FTA state symbol Constraint ->
    Maybe (FTA.FTA (state, Context symbol) (Parented symbol) Constraint)
withParents root automaton
    | any (any ((/= noConstraint) . FTA.transitionConstraint)) (FTA.transitionTable automaton) = Nothing
    | otherwise =
        Just
            $ fromRight (error "withParents: the states of a valid automaton give a valid automaton")
            $ FTA.mkFTA start
            $ explore Set.empty [start] []
  where
    start = (FTA.initialState automaton, root)
    rowOf (state, context) =
        [ FTA.Transition
            ((symbol, length children), context)
            [(child, Just ((symbol, length children), position)) | (position, child) <- zip [0 ..] children]
            noConstraint
        | FTA.Transition symbol children _ <- FTA.transitionsFrom automaton state
        ]
    explore _ [] rows = rows
    explore seen (state : pending) rows
        | Set.member state seen = explore seen pending rows
        | otherwise =
            let row = rowOf state
             in explore (Set.insert state seen) (concatMap FTA.transitionChildren row <> pending) ((state, row) : rows)

-- | The labelling of a term in the labelled automaton, with the context of the root.
labelParents :: Context symbol -> Term symbol -> Term (Parented symbol)
labelParents context (Term.Node symbol children) =
    Term.Node
        ((symbol, length children), context)
        [labelParents (Just ((symbol, length children), position)) child | (position, child) <- zip [0 ..] children]

-- | The term of a labelled term.
unlabelParents :: Term (Parented symbol) -> Term symbol
unlabelParents = fmap (fst . fst)

{- | The labelling of a prefix of tokens in preorder, with the context of the
root. 'Nothing' when a token comes after a complete term.
-}
labelPrefix :: Context symbol -> [Token symbol] -> Maybe [Token (Parented symbol)]
labelPrefix root = go [root]
  where
    go _ [] = Just []
    go [] _ = Nothing
    go (context : pending) ((symbol, count) : rest) =
        ((((symbol, count), context), count) :)
            <$> go ([Just ((symbol, count), position) | position <- [0 .. count - 1]] <> pending) rest
