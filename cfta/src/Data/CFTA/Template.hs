{- | Patterns over the terms of a language.

A 'Template' matches a term by its root symbol and child positions. 'Hole'
matches any complete subtree. Exact patterns require the complete child list;
prefix patterns constrain only the leading children. 'restrict' keeps exactly
the matching terms of an interned graph, and 'restrictFTA' those of an
explicit-state automaton. 'exclude' keeps exactly the terms that match none
of some templates, and it keeps one run for each run of the input whose term
it keeps, so that counts and ranks over the result stay exact. None of them
interprets transition annotations; a constraint theory reduces its
constraints afterwards.
-}
module Data.CFTA.Template (
    Template (..),
    matchesTemplate,
    matchesNone,
    restrict,
    restrictFTA,
    exclude,
) where

import Data.Either (fromRight)
import Data.Hashable (Hashable)
import Data.List (nub, partition)
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
is a run of exactly one copy: the result is as unambiguous as the input,
and counts and ranks over it are exact.

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
        Node edges -> Node (concatMap (refineEdge wanted' (nub unwanted)) edges)
        Rec _ -> error "exclude: unexpected free recursive reference"
  where
    wanted' = nub (filter (not . trivial) wanted)

-- | The copies of an edge whose terms match every wanted template and no unwanted one.
refineEdge ::
    (Hashable symbol, Typeable symbol) =>
    [Template symbol] -> [Template symbol] -> Edge symbol -> [Edge symbol]
refineEdge wanted unwanted edge = case traverse childrenOf wanted of
    Nothing -> []
    Just wantedChildren ->
        map
            (setChildren edge)
            (copies (zip3 [0 ..] children (transposed wantedChildren)) (mapMaybe childrenOf unwanted))
  where
    children = edgeChildren edge
    childrenOf template = childTemplates template (edgeSymbol edge) (Arity (length children))
    transposed rows = [[row !! index | row <- rows] | index <- [0 .. length children - 1]]
    -- For each child in turn, the unwanted templates that every earlier
    -- child matched (alive) split into those that this child matches too
    -- and those that it does not. A template whose part here is a hole
    -- stays alive; one whose later parts are all holes must die here. A
    -- copy with a template alive after the last child has no terms.
    copies [] alive = [[] | null alive]
    copies ((index, child, wantedHere) : rest) alive =
        [ refine (wantedHere <> map (!! index) kept) (map (!! index) killed) child : later
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
