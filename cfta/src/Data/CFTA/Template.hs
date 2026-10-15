{- | Patterns over the terms of a language.

A 'Template' matches a term by its root symbol and child positions. 'Hole'
matches any complete subtree. Exact patterns require the complete child list;
prefix patterns constrain only the leading children. 'restrict' keeps exactly
the matching terms of an interned graph, and 'restrictFTA' those of an
explicit-state automaton. 'exclude' keeps exactly the terms of an interned
graph that match none of some templates, and 'excludeFTA' those of an
explicit-state automaton. An unambiguous input gives an unambiguous result,
so counts and ranks over it stay exact. None of them interprets transition
annotations; a constraint theory reduces its constraints afterwards.
-}
module Data.CFTA.Template (
    Template (..),
    matchesTemplate,
    matchesNone,
    restrict,
    restrictFTA,
    exclude,
    excludeFTA,
    Obligation (..),
) where

import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import Data.Hashable (Hashable)
import Data.List (nub, partition, sort)
import Data.Maybe (mapMaybe)
import Data.Typeable (Typeable)

import Data.CFTA (FTA, Transition (..))
import qualified Data.CFTA as FTA
import Data.CFTA.Index (Arity (..))
import Data.CFTA.Internal.Tree (explore)
import Data.CFTA.Interned.Operations (nodeEdges)
import Data.CFTA.Interned.Type
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | Pattern over first-order terms.
data Template symbol
    = -- | Match any complete subtree.
      Hole
    | -- | Match any root symbol with exactly these children.
      AnyNode ![Template symbol]
    | -- | Match this root symbol with exactly these children.
      TemplateNode !symbol ![Template symbol]
    | -- | Match any root symbol whose children begin with this prefix.
      AnyPrefix ![Template symbol]
    | -- | Match this root symbol when its children begin with this prefix.
      TemplatePrefix !symbol ![Template symbol]
    deriving (Eq, Ord, Read, Show)

{- | The pattern for each child of a constructor with the given symbol and
arity, or 'Nothing' when the constructor cannot match.
-}
childTemplates :: (Eq symbol) => Template symbol -> symbol -> Arity -> Maybe [Template symbol]
childTemplates Hole _ (Arity count) = Just (replicate count Hole)
childTemplates (AnyNode templates) _ arity = exact templates arity
childTemplates (TemplateNode symbol templates) actual arity
    | symbol == actual = exact templates arity
    | otherwise = Nothing
childTemplates (AnyPrefix templates) _ arity = prefix templates arity
childTemplates (TemplatePrefix symbol templates) actual arity
    | symbol == actual = prefix templates arity
    | otherwise = Nothing

exact, prefix :: [Template symbol] -> Arity -> Maybe [Template symbol]
exact templates (Arity count)
    | length templates == count = Just templates
    | otherwise = Nothing
prefix templates (Arity count)
    | length templates <= count = Just (templates ++ replicate (count - length templates) Hole)
    | otherwise = Nothing

-- | Test a concrete term against a template.
matchesTemplate :: (Eq symbol) => Template symbol -> Term symbol -> Bool
matchesTemplate template (Term.Node symbol children) =
    maybe False (\templates -> and (zipWith matchesTemplate templates children)) $
        childTemplates template symbol (Arity (length children))

-- | Whether a concrete term matches none of the templates.
matchesNone :: (Eq symbol) => [Template symbol] -> Term symbol -> Bool
matchesNone templates term = not (any (`matchesTemplate` term) templates)

-- | Keep exactly the terms of an interned graph that match a template.
restrict ::
    (Hashable symbol, Typeable symbol) =>
    Template symbol -> Node symbol -> Node symbol
restrict Hole node = node
restrict (AnyPrefix []) node = node
restrict _ EmptyNode = EmptyNode
restrict template node@(Mu _) = restrict template (Node $ nodeEdges node)
restrict template node@(InternedUnion _) = restrict template (Node $ nodeEdges node)
restrict template (Node edges) = Node (mapMaybe (restrictEdge template) edges)
restrict _ (Rec _) = error "restrict: unexpected free recursive reference"

restrictEdge ::
    (Hashable symbol, Typeable symbol) =>
    Template symbol -> Edge symbol -> Maybe (Edge symbol)
restrictEdge Hole edge = Just edge
restrictEdge (AnyPrefix []) edge = Just edge
restrictEdge template edge =
    (\templates -> setChildren edge (zipWith restrict templates children))
        <$> childTemplates template (edgeSymbol edge) (Arity (length children))
  where
    children = edgeChildren edge

{- | Keep exactly the terms of an automaton that match a template.

Each result state pairs a source state with the pattern its terms must
match. Only reachable pairs are built.
-}
restrictFTA ::
    (Ord state, Ord symbol) =>
    Template symbol -> FTA state symbol annotation -> FTA (state, Template symbol) symbol annotation
restrictFTA template automaton =
    -- The input is ranked, so the restriction is ranked and validation cannot fail.
    fromRight (error "restrictFTA: the restriction of a ranked automaton is ranked")
        $ FTA.mkFTA initial
        $ explore restrictTransitions transitionChildren initial
  where
    initial = (FTA.initialState automaton, template)

    restrictTransitions (state, wanted) = mapMaybe (restrictTransition wanted) (FTA.transitionsFrom automaton state)
    restrictTransition wanted transition =
        (\templates -> transition{transitionChildren = zip (transitionChildren transition) templates})
            <$> childTemplates wanted (transitionSymbol transition) (Arity $ length $ transitionChildren transition)

{- | Keep exactly the terms of an interned graph that match none of the
templates at the root, as 'matchesNone' says.

The result splits an edge by what its children match. For each child in
turn, each template that the children before it all matched either matches
this child too or not, and the child gets the templates that it must match
and those that it must not. A copy of the edge whose children match all of
some template's children has no terms, and it goes. The children of a term
match what they match, so each run of the input whose term the result keeps
is a run of exactly one copy. An unambiguous input gives an unambiguous
result, so counts and ranks over it are exact. For an ambiguous input, the
number of runs of a term can change.

The result differs from the input only as deep as the templates. Below
them, it shares the input's nodes, and it unfolds a 'Mu' only that deep, as
'restrict' does. An edge with @k@ children and @m@ templates that constrain
more than one of them can have up to @2^m@ copies for each such child, but
a template whose later parts are all holes must die at its last constrained
child, so there it gives no choice.
-}
exclude ::
    (Hashable symbol, Typeable symbol) =>
    [Template symbol] -> Node symbol -> Node symbol
exclude = refine []

{- | The terms of a node that match every template of the first list and none
of the second.
-}
refine ::
    (Hashable symbol, Typeable symbol) =>
    [Template symbol] -> [Template symbol] -> Node symbol -> Node symbol
refine wanted unwanted node
    | any trivial unwanted = EmptyNode
    | null wanted' && null unwanted = node
    | otherwise = case node of
        EmptyNode -> EmptyNode
        Mu _ -> refine wanted' unwanted (Node $ nodeEdges node)
        InternedUnion _ -> refine wanted' unwanted (Node $ nodeEdges node)
        Node edges ->
            Node
                [ setChildren edge (zipWith (\(wanted'', unwanted') child -> refine wanted'' unwanted' child) parts (edgeChildren edge))
                | edge <- edges
                , parts <- edgeCopies wanted' (nub unwanted) (edgeSymbol edge) (length (edgeChildren edge))
                ]
        Rec _ -> error "exclude: unexpected free recursive reference"
  where
    wanted' = nub (filter (not . trivial) wanted)

{- | What the terms of a state of 'excludeFTA' must match: every template of
the first list, and none of the second.
-}
data Obligation symbol = Obligation ![Template symbol] ![Template symbol]
    deriving (Eq, Ord, Read, Show)

{- | Keep exactly the terms of an automaton that match none of the templates
at the root, as 'exclude' does for an interned graph.

Each result state pairs a source state with what its terms must match and
must not ('Obligation'). A transition splits as an edge does in 'exclude'
('edgeCopies'). Only reachable pairs are built.
-}
excludeFTA ::
    (Ord state, Ord symbol) =>
    [Template symbol] -> FTA state symbol annotation -> FTA (state, Obligation symbol) symbol annotation
excludeFTA templates automaton =
    -- The input is ranked, so the result is ranked and validation cannot fail.
    fromRight (error "excludeFTA: the exclusion from a ranked automaton is ranked")
        $ FTA.mkFTA initial
        $ explore excludeTransitions transitionChildren initial
  where
    initial = (FTA.initialState automaton, obligation [] templates)
    excludeTransitions (state, Obligation wanted unwanted)
        | any trivial unwanted = []
        | otherwise =
            [ transition
                { transitionChildren =
                    zipWith (\child (wanted', unwanted') -> (child, obligation wanted' unwanted')) (transitionChildren transition) parts
                }
            | transition <- FTA.transitionsFrom automaton state
            , parts <- edgeCopies wanted unwanted (transitionSymbol transition) (length (transitionChildren transition))
            ]
    -- One form for equal obligations, so that equal states are one state.
    obligation wanted unwanted = Obligation (sort (nubOrd (filter (not . trivial) wanted))) (sort (nubOrd unwanted))

{- | The copies of an edge with a symbol and a number of children whose terms
match every wanted template and no unwanted one: for each copy, what each
child must match and must not.

For each child in turn, the unwanted templates that every earlier child
matched (alive) split into those that this child matches too and those
that it does not. A template whose part here is a hole stays alive; one
whose later parts are all holes must die here. A copy with a template alive
after the last child has no terms.
-}
edgeCopies ::
    (Eq symbol) => [Template symbol] -> [Template symbol] -> symbol -> Int -> [[([Template symbol], [Template symbol])]]
edgeCopies wanted unwanted symbol count = case traverse childrenOf wanted of
    Nothing -> []
    Just wantedChildren -> copies (zip [0 ..] (transposed wantedChildren)) (mapMaybe childrenOf unwanted)
  where
    childrenOf template = childTemplates template symbol (Arity count)
    transposed rows = [[row !! index | row <- rows] | index <- [0 .. count - 1]]
    copies [] alive = [[] | null alive]
    copies ((index, wantedHere) : rest) alive =
        [ (wantedHere <> map (!! index) kept, map (!! index) killed) : later
        | (chosen, notChosen) <- splits mayLive
        , let kept = forced <> chosen
              killed = mustDie <> notChosen
        , later <- copies rest kept
        ]
      where
        (forced, free) = partition (\parts -> trivial (parts !! index)) alive
        (mustDie, mayLive) = partition (all trivial . drop (index + 1)) free
    splits [] = [([], [])]
    splits (value : rest) = concat [[(value : chosen, notChosen), (chosen, value : notChosen)] | (chosen, notChosen) <- splits rest]

-- | Whether a template matches every term.
trivial :: Template symbol -> Bool
trivial Hole = True
trivial (AnyPrefix []) = True
trivial _ = False
