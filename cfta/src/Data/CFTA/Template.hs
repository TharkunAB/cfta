{- | Patterns over the terms of a language.

A 'Template' matches a term by its root symbol and child positions. 'Hole'
matches any complete subtree. Exact patterns require the complete child list;
prefix patterns constrain only the leading children. 'restrict' keeps exactly
the matching terms of an interned graph, and 'restrictFTA' those of an
explicit-state automaton. 'exclude' keeps exactly the terms of an interned
graph that match none of some templates at the root, and 'excludeFTA' those
of an explicit-state automaton. 'excludeAnywhere' keeps those of an
interned graph of which no subterm matches one. An unambiguous input gives
an unambiguous result, so counts and ranks over it stay exact. None of them
interprets transition annotations; a constraint theory reduces its
constraints afterwards. 'preorderPrefix' makes the template of a prefix of
a term in preorder.
-}
module Data.CFTA.Template (
    Template (..),
    matchesTemplate,
    matchesNone,
    matchesNowhere,
    restrict,
    restrictFTA,
    exclude,
    excludeFTA,
    excludeAnywhere,
    Obligation (..),
    preorderPrefix,
) where

import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import Data.Hashable (Hashable)
import Data.List (nub, partition, sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import Data.Typeable (Typeable)

import Data.CFTA (FTA, Transition (..))
import qualified Data.CFTA as FTA
import Data.CFTA.Index (Arity (..))
import Data.CFTA.Internal.Tree (explore)
import Data.CFTA.Interned (fromRows)
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
excludeFTA = excludeBelow []

{- | Keep exactly the terms of an automaton that match none of the second
templates at the root, and of which no proper subterm matches one of the
first templates.
-}
excludeBelow ::
    (Ord state, Ord symbol) =>
    [Template symbol] ->
    [Template symbol] ->
    FTA state symbol annotation ->
    FTA (state, Obligation symbol) symbol annotation
excludeBelow everywhere templates automaton =
    -- The input is ranked, so the result is ranked and validation cannot fail.
    fromRight (error "excludeBelow: the exclusion from a ranked automaton is ranked") $
        uncurry FTA.mkFTA (obligationRows everywhere (FTA.transitionsFrom automaton) templates (FTA.initialState automaton))

{- | The pairs of a state and an 'Obligation' that a state reaches, with
their transitions, when its terms must match none of the second templates
at the root and none of the first at a proper subterm: the first pair, and
the rows. A transition splits as an edge does in 'exclude' ('edgeCopies').
-}
obligationRows ::
    (Ord state, Ord symbol) =>
    [Template symbol] ->
    (state -> [Transition state symbol annotation]) ->
    [Template symbol] ->
    state ->
    ((state, Obligation symbol), [((state, Obligation symbol), [Transition (state, Obligation symbol) symbol annotation])])
obligationRows everywhere transitionsOf templates state = (initial, explore copies transitionChildren initial)
  where
    initial = (state, obligation [] templates)
    copies (state', Obligation wanted unwanted)
        | any trivial unwanted = []
        | otherwise =
            [ transition
                { transitionChildren =
                    zipWith
                        (\child (wanted', unwanted') -> (child, obligation wanted' (unwanted' <> everywhere)))
                        (transitionChildren transition)
                        parts
                }
            | transition <- transitionsOf state'
            , parts <- edgeCopies wanted unwanted (transitionSymbol transition) (length (transitionChildren transition))
            ]
    -- One form for equal obligations, so that equal states are one state.
    obligation wanted unwanted = Obligation (sort (nubOrd (filter (not . trivial) wanted))) (sort (nubOrd unwanted))

{- | Keep exactly the terms of an interned graph of which no subterm matches
one of the templates, as 'matchesNowhere' says.

Each position of a term gets the templates again, so the result reaches the
whole automaton. Its states pair a node of the input with what the terms of
a position must match and must not ('Obligation'), as for 'excludeFTA'.
Only the reachable pairs are built, and 'fromRows' interns them: a cycle of
pairs gets a 'Mu', so a recursive input gives a recursive result, and each
node is built once for each set of enclosing binders. The obligations are
subsets of the templates' parts, so there are finitely many. The symbols
need no consistent arity. As for 'exclude', each run of the input whose
term the result keeps is a run of exactly one copy of an edge, and an
unambiguous input gives an unambiguous result.
-}
excludeAnywhere ::
    (Ord symbol, Hashable symbol, Typeable symbol) =>
    [Template symbol] -> Node symbol -> Node symbol
excludeAnywhere templates root
    | not (Set.null (freeVars root)) = error "excludeAnywhere: unexpected free recursive reference"
    | otherwise = uncurry fromRows (Map.fromList <$> obligationRows templates transitionsOf templates root)
  where
    transitionsOf node = [Transition (edgeSymbol edge) (edgeChildren edge) (edgeConstraint edge) | edge <- nodeEdges node]

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

-- | Whether no subterm of a concrete term matches one of the templates.
matchesNowhere :: (Eq symbol) => [Template symbol] -> Term symbol -> Bool
matchesNowhere templates term@(Term.Node _ children) = matchesNone templates term && all (matchesNowhere templates) children

{- | The template of a prefix of a term in preorder: each node by its symbol
and its number of children, the first node first. The template matches
exactly the terms whose preorder starts with these nodes: the children that
the prefix does not reach are holes. So @[(f, 2), (g, 0)]@ gives
@TemplateNode f [TemplateNode g [], Hole]@, and @[]@ gives 'Hole'.
-}
preorderPrefix :: [(symbol, Int)] -> Template symbol
preorderPrefix = fst . node
  where
    node [] = (Hole, [])
    node ((symbol, count) : rest) = let (children, rest') = nodes count rest in (TemplateNode symbol children, rest')
    nodes 0 rest = ([], rest)
    nodes count rest =
        let (child, rest') = node rest
            (children, rest'') = nodes (count - 1 :: Int) rest'
         in (child : children, rest'')
