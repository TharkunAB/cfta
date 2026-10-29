{- | Patterns over the terms of a language.

A 'Template' matches a term by its root symbol and child positions. 'Hole'
matches any complete subtree. Exact patterns require the complete child list;
prefix patterns constrain only the leading children. 'restrict' keeps exactly
the matching terms of an interned graph, and 'restrictFTA' those of an
explicit-state automaton. 'exclude' keeps exactly the terms of an interned
graph that match none of some templates at the root, and 'excludeFTA' those
of an explicit-state automaton. 'excludeAnywhere' and 'excludeAnywhereFTA'
keep those of which no subterm matches one. An unambiguous input gives an
unambiguous result, so counts and ranks over it stay exact. None of them
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
    excludeAnywhereFTA,
    Exclusion (..),
    excludeAllFTA,
    Obligation (..),
    excludePrefixesFTA,
    Position (..),
    preorderPrefix,
) where

import Control.Monad (foldM, zipWithM)
import Control.Monad.State.Strict (evalState, gets, modify', runState)
import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import Data.Foldable (toList)
import Data.Hashable (Hashable (..))
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import Data.List (partition, sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust, isNothing, mapMaybe)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import Data.Typeable (Typeable)

import Data.CFTA (FTA, Transition (..))
import qualified Data.CFTA as FTA
import Data.CFTA.Index (Arity (..))
import Data.CFTA.Internal.Tree (explore)
import Data.CFTA.Interned (fromRows)
import Data.CFTA.Interned.Memo (memo)
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
child, so there it gives no choice. A part without holes matches one term
only, so a child has one copy for each such part and one for none, not one
for each subset of the templates that have such parts. For templates that
fix their earlier children, as the preorder prefixes of 'preorderPrefix'
do, this is all the choice there is. A template also stays alive into a
child only when its part, with the other parts that the child must match,
can match the root of an edge of the child, so a copy that no term of the
child can fill is not made. Many templates whose parts at a child share a
root that the child has can still give @2^m@ copies.

Templates must be finite and total, and symbol Eq and Ord must agree.
Exclusion prepares their subtrees once. This can evaluate a template part
before the input graph reaches its position.
-}
exclude ::
    (Ord symbol, Hashable symbol, Typeable symbol) =>
    [Template symbol] -> Node symbol -> Node symbol
exclude templates = walk
  where
    (hole, prepared) = prepareTemplates templates
    -- One application of 'refine' for all the nodes, so that they share its table.
    refined = refine originalTemplate (preparedChildren hole)
    walk node
        | any trivial templates = EmptyNode
        | null templates = node
        | EmptyNode <- node = EmptyNode
        | otherwise = refined [] prepared node

{- | A structural template with its catalog identifier and prepared children.
Identifiers preserve structural template order within one catalog. Parts from
different catalogs must not be mixed.
-}
data PreparedTemplate symbol = PreparedTemplate !Int !(Template symbol) [PreparedTemplate symbol]

instance Eq (PreparedTemplate symbol) where
    PreparedTemplate left _ _ == PreparedTemplate right _ _ = left == right

instance Ord (PreparedTemplate symbol) where
    compare (PreparedTemplate left _ _) (PreparedTemplate right _ _) = compare left right

instance Hashable (PreparedTemplate symbol) where
    hashWithSalt salt (PreparedTemplate identifier _ _) = hashWithSalt salt identifier

-- | The original template of a prepared part.
originalTemplate :: PreparedTemplate symbol -> Template symbol
originalTemplate (PreparedTemplate _ template _) = template

{- | Prepare the finite subtree catalog, including Hole, for one exclusion.
Templates must be finite and total, and symbol Eq and Ord must agree. The
catalog must fit in Int. Catalog construction can force otherwise unused
parts earlier. It does not inspect the input graph or combine obligations.
-}
prepareTemplates :: (Ord symbol) => [Template symbol] -> (PreparedTemplate symbol, [PreparedTemplate symbol])
prepareTemplates templates = (catalog Map.! Hole, map (catalog Map.!) templates)
  where
    catalog =
        Map.fromList
            [ (template, PreparedTemplate identifier template (map (catalog Map.!) (children template)))
            | (identifier, template) <- zip [0 ..] (Set.toAscList (Set.fromList (Hole : concatMap subtrees templates)))
            ]
    subtrees template = template : concatMap subtrees (children template)
    children Hole = []
    children (AnyNode parts) = parts
    children (TemplateNode _ parts) = parts
    children (AnyPrefix parts) = parts
    children (TemplatePrefix _ parts) = parts

{- | Select already prepared children with the original shape check. Only
prefix padding and Hole introduce parts outside the stored child list.
-}
preparedChildren ::
    (Eq symbol) => PreparedTemplate symbol -> PreparedTemplate symbol -> symbol -> Arity -> Maybe [PreparedTemplate symbol]
preparedChildren hole (PreparedTemplate _ template children) symbol arity@(Arity count) =
    case childTemplates template symbol arity of
        Nothing -> Nothing
        Just _ -> Just (take count (children <> repeat hole))

{- | The terms of a node that match every template of the first list and none
of the second. Parts keep their original templates and child projections.
Their Ord instance must agree with structural template order. A table for
each application of the first two arguments shares the result of a node
and its two lists of parts, so a node that many edges reach with the same
parts is refined once.
-}
refine ::
    (Ord part, Hashable part, Ord symbol, Hashable symbol, Typeable symbol) =>
    (part -> Template symbol) ->
    (part -> symbol -> Arity -> Maybe [part]) ->
    [part] ->
    [part] ->
    Node symbol ->
    Node symbol
refine original childrenOf = \wanted unwanted node -> walk (wanted, unwanted, node)
  where
    walk = memo walk'
    -- The copies of an edge depend only on the parts, the symbol, and the
    -- shapes of the children, which many edges share.
    copiesOf = memo (\(wanted', unwanted', symbol, shapes) -> edgeCopiesWith original childrenOf wanted' unwanted' symbol shapes)
    walk' (wanted, unwanted, node)
        | any (trivial . original) unwanted = EmptyNode
        | null wanted' && null unwanted = node
        | otherwise = case node of
            EmptyNode -> EmptyNode
            Mu _ -> walk (wanted', unwanted, Node $ nodeEdges node)
            InternedUnion _ -> walk (wanted', unwanted, Node $ nodeEdges node)
            Node edges ->
                Node
                    [ setChildren edge (zipWith (\(wanted'', unwanted') child -> walk (wanted'', unwanted', child)) parts (edgeChildren edge))
                    | edge <- edges
                    , parts <- copiesOf (wanted', nubOrd unwanted, edgeSymbol edge, map shapesOf (edgeChildren edge))
                    ]
            Rec _ -> error "exclude: unexpected free recursive reference"
      where
        wanted' = nubOrd (filter (not . trivial . original) wanted)
    shapesOf child = [(edgeSymbol edge, length (edgeChildren edge)) | edge <- nodeEdges child]

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
    -- The rows give each pair that they reach a row, so validation cannot fail.
    fromRight (error "excludeBelow: the rows of the exclusion are not closed") $
        uncurry FTA.mkFTA (obligationRows everywhere (FTA.transitionsFrom automaton) templates (FTA.initialState automaton))

-- | A template that rejects a term: when the whole term matches it, or when a subterm matches it.
data Exclusion symbol
    = -- | Reject a term that matches the template.
      AtRoot !(Template symbol)
    | -- | Reject a term with a subterm that matches the template.
      Anywhere !(Template symbol)
    deriving (Eq, Ord, Read, Show)

{- | Keep exactly the terms of an automaton that no exclusion rejects:
'excludeFTA' with the templates at the root, then 'excludeAnywhereFTA' with
the templates anywhere. These keep only the transitions whose children can
have terms. Without exclusions, the result is the input with each state paired
with empty obligations, so it keeps every row and the order of the states.
-}
excludeAllFTA ::
    (Ord state, Ord symbol) =>
    [Exclusion symbol] ->
    FTA state symbol annotation ->
    FTA ((state, Obligation symbol), Obligation symbol) symbol annotation
excludeAllFTA [] = FTA.mapStates (\state -> ((state, Obligation [] []), Obligation [] []))
excludeAllFTA exclusions =
    excludeAnywhereFTA [template | Anywhere template <- exclusions] . excludeFTA [template | AtRoot template <- exclusions]

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
            , parts <- edgeCopies wanted unwanted (transitionSymbol transition) (map shapesOf (transitionChildren transition))
            ]
    shapesOf child = [(transitionSymbol transition, length (transitionChildren transition)) | transition <- transitionsOf child]
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

{- | Keep exactly the terms of an automaton of which no subterm matches one
of the templates, as 'excludeAnywhere' does for an interned graph.

The states are as for 'excludeFTA', and each child gets the templates
again. The obligations are finite, so the result is finite, and a cycle of
the input gives a cycle of the result.
-}
excludeAnywhereFTA ::
    (Ord state, Ord symbol) =>
    [Template symbol] -> FTA state symbol annotation -> FTA (state, Obligation symbol) symbol annotation
excludeAnywhereFTA templates = excludeBelow templates templates

{- | A place in the preorder of a term for 'excludePrefixesFTA': a node of
the minimal automaton of the prefixes, or 'Free' after a node that no
prefix continues with. The minimal automaton is the trie of the prefixes
with each set of equal subtries as one node, so two places with the same
continuations are one node.
-}
data Position = Free | At !Int
    deriving (Eq, Ord, Read, Show)

{- | Keep exactly the terms of an automaton whose preorder, each node as its
symbol and its number of children, starts with none of the prefixes, as
@excludeFTA (map preorderPrefix prefixes)@ does. It is for many prefixes,
such as the dead prefixes of a search.

A result state is a state of the input, the 'Position' where the preorder
of its terms begins, and the position where it ends ('Nothing': any, for the
root). A subtree ends 'Free' unless its whole preorder is a path of the
prefixes' automaton; then it ends at the node of that path. So a transition
has a copy for each sequence of the positions where its children end, and a
term fixes them: each run of the input whose term the result keeps is a run
of exactly one copy, and an unambiguous input gives an unambiguous result.
A copy keeps the transition's annotation. A result state holds two nodes,
not a set of prefixes, so a comparison of two states is cheap.
-}
excludePrefixesFTA ::
    (Ord state, Ord symbol) =>
    [[(symbol, Int)]] ->
    FTA state symbol annotation ->
    FTA (state, Position, Maybe Position) symbol annotation
excludePrefixesFTA prefixes automaton =
    -- The input is ranked, so the result is ranked and validation cannot fail.
    fromRight (error "excludePrefixesFTA: the exclusion from a ranked automaton is ranked") $
        FTA.mkFTA initial (evalState (walk Set.empty [initial] []) Map.empty)
  where
    initial = (FTA.initialState automaton, maybe Free At root, Nothing)
    -- The minimal automaton of the prefixes. A node maps a token to the next
    -- node, or to 'Nothing' when the token completes a prefix. The root is
    -- 'Nothing' when the empty prefix is one of the prefixes.
    (root, nodes) =
        fmap (\table -> IntMap.fromList [(node, next) | (next, node) <- Map.toList table]) (runState (build prefixes) Map.empty)
      where
        build paths
            | any null paths = pure Nothing
            | otherwise = do
                next <- traverse build (Map.fromListWith (<>) [(token, [rest]) | token : rest <- paths])
                known <- gets (Map.lookup next)
                case known of
                    Just node -> pure (Just node)
                    Nothing -> do
                        node <- gets Map.size
                        modify' (Map.insert next node)
                        pure (Just node)
    -- The position after a token, or 'Nothing' when the token completes a prefix.
    step Free _ = Just Free
    step (At node) token = case Map.lookup token (IntMap.findWithDefault Map.empty node nodes) of
        Nothing -> Just Free
        Just next -> At <$> next
    tokenOf transition = (transitionSymbol transition, length (transitionChildren transition))
    -- The reachable states and their transitions, with the ends of each pair of a state and a position as a memo.
    walk _ [] rows = pure rows
    walk seen (key : pending) rows
        | Set.member key seen = walk seen pending rows
        | otherwise = do
            row <- transitionsOf key
            walk (Set.insert key seen) (concatMap transitionChildren row <> pending) ((key, row) : rows)
    transitionsOf (state, entry, exit)
        | isNothing root = pure []
        | otherwise =
            concat
                <$> sequence
                    [ case step entry (tokenOf transition) of
                        Nothing -> pure []
                        Just start -> map (\children -> transition{transitionChildren = children}) <$> copies start exit (transitionChildren transition)
                    | transition <- FTA.transitionsFrom automaton state
                    ]
    -- The children of the copies: each child with where it begins and ends,
    -- the last one ending at the transition's end. A child that begins
    -- 'Free' ends 'Free'.
    copies here exit [] = pure [[] | maybe True (== here) exit]
    copies here exit [child] = case exit of
        Nothing
            | here == Free -> pure [[(child, Free, Just Free)]]
            | otherwise -> pure [[(child, here, Nothing)]]
        Just end -> do
            possible <- endsOf child here
            pure [[(child, here, Just end)] | Set.member end possible]
    copies here exit (child : rest) = do
        possible <- endsOf child here
        concat <$> mapM (\end -> map ((child, here, Just end) :) <$> copies end exit rest) (Set.toList possible)
    -- Where the terms of a state can end when they begin at a position.
    endsOf _ Free = pure (Set.singleton Free)
    endsOf state here = do
        known <- gets (Map.lookup (state, here))
        case known of
            Just result -> pure result
            Nothing -> do
                result <-
                    Set.unions
                        <$> sequence
                            [ maybe (pure Set.empty) (\start -> foldEnds start (transitionChildren transition)) (step here (tokenOf transition))
                            | transition <- FTA.transitionsFrom automaton state
                            ]
                modify' (Map.insert (state, here) result)
                pure result
    foldEnds start children =
        foldl
            (\positions child -> positions >>= \set -> Set.unions <$> mapM (endsOf child) (Set.toList set))
            (pure (Set.singleton start))
            children

{- | The copies of an edge with a symbol and its children whose terms match
every wanted template and no unwanted one: for each copy, what each child
must match and must not. A child is given by its shapes: the symbol and the
number of children of each of its edges.

For each child in turn, the unwanted templates that every earlier child
matched (alive) split into those that this child matches too and those
that it does not. A template whose part here is a hole stays alive; one
whose later parts are all holes must die here. A copy with a template alive
after the last child has no terms. A part without holes ('ground') matches
one term only, so the child equals at most one ground part: the split has a
copy for each ground part, which keeps the templates of that part, and a
copy for none, which kills them all. The other templates that may stay
alive split over every subset.

A copy keeps only templates whose parts the child can match together: the
parts that the child must match, wanted or kept, must all fit the root of
one shape of the child ('childTemplates'). Another copy has no terms, so it
is not made, and an edge whose wanted parts fit no shape of a child has no
copies. A part that fits no shape of the child is not passed to it as a part
that it must not match: no term of the child matches it. Many parts that fit
one shape, for example parts with one root symbol that the child has, still
split over every subset.
-}
edgeCopies ::
    (Ord symbol) =>
    [Template symbol] ->
    [Template symbol] ->
    symbol ->
    [[(symbol, Int)]] ->
    [[([Template symbol], [Template symbol])]]
edgeCopies = edgeCopiesWith id childTemplates

{- | Split an edge with one representation of structural template parts.
The projection must preserve childTemplates and structural template order.
The result keeps the original obligation lists and their order.
-}
edgeCopiesWith ::
    (Ord part, Ord symbol) =>
    (part -> Template symbol) ->
    (part -> symbol -> Arity -> Maybe [part]) ->
    [part] ->
    [part] ->
    symbol ->
    [[(symbol, Int)]] ->
    [[([part], [part])]]
edgeCopiesWith original childParts wanted unwanted symbol shapes = case traverse childrenOf wanted of
    Nothing -> []
    Just wantedChildren -> copies (zip3 [0 ..] (transposed wantedChildren) shapes) unwantedChildren
  where
    count = length shapes
    childrenOf template = childParts template symbol (Arity count)
    transposed rows = [[row !! index | row <- rows] | index <- [0 .. count - 1]]
    unwantedChildren = mapMaybe childrenOf unwanted
    -- For finite templates and lawful symbol Ord, IDs agree if and only if
    -- the child parts are equal. Each map is demanded only when needed.
    partIdentifiers =
        [ Map.fromList [(parts !! index, identifier) | (identifier, parts) <- zip [0 ..] unwantedChildren]
        | index <- [0 .. count - 1]
        ]
    copies [] alive = [[] | null alive]
    copies ((index, wantedHere, shapesHere) : rest) alive =
        [ (wantedHere <> map (!! index) kept, filter (\part -> not (null (fits shapesHere [part]))) (map (!! index) killed))
            : later
        | (kept, killed) <- choices
        , later <- copies rest kept
        ]
      where
        (forced, free) = partition (\parts -> trivial (original (parts !! index))) alive
        (mustDie, mayLive) = partition (all (trivial . original) . drop (index + 1)) free
        -- The child equals at most one ground part. If it equals one, the
        -- templates of that part stay alive, and the other ground parts
        -- cannot match it, so they need not die here. A part that a
        -- template which must die has too cannot stay alive.
        (fixed, open) = partition (ground . original . (!! index)) mayLive
        (groundDying, openDying) = partition (ground . original . (!! index)) mustDie
        -- ID sets track the unchanged chosen/notChosen lists. They replace
        -- only membership checks. Keep the original templates and order.
        identifiedOpen = [(parts, (partIdentifiers !! index) Map.! (parts !! index)) | parts <- open]
        -- Append singleton rows without copying each accumulated prefix.
        -- Convert each used group to a list once. For finite total input,
        -- each group must fit in Int. Its order and duplicates are unchanged.
        -- Keep conversion lazy
        -- so a rejected group does not need its obligation list.
        groups = Map.fromListWith (flip (<>)) [(parts !! index, Seq.singleton parts) | parts <- fixed]
        dying = Set.fromList (map (!! index) groundDying)
        -- The shapes that the parts which the child must match all fit.
        base = fits shapesHere (wantedHere <> map (!! index) forced)
        choices
            | null base = []
            | otherwise = case foldM meetTemplate Hole (map original (wantedHere <> map (!! index) forced)) of
                Nothing -> []
                Just required ->
                    [ (forced <> chosen, mustDie <> fixed <> notChosen)
                    | ((chosen, notChosen), _, _, _, _) <- splits base required identifiedOpen
                    ]
                        <> [ (forced <> group <> chosen, openDying <> notChosen)
                           | (part, rows) <- Map.toList groups
                           , Set.notMember part dying
                           , let group = toList rows
                           , Just combined <- [meetTemplate required (original part)]
                           , let narrowed = fits base [part]
                           , not (null narrowed)
                           , ((chosen, notChosen), _, _, _, _) <- splits narrowed combined identifiedOpen
                           ]
        -- Carry the positive conjunction through the same tail-first split.
        -- A failed meet removes only the impossible kept alternative.
        -- A child cannot match and fail the same part. Remove only such
        -- choices. Keep the order and obligation lists of the other choices.
        -- This preserves the complete finite-term language. It does not prove
        -- that every recursive cutoff stream remains equal.
        splits fitting required [] = [(([], []), fitting, required, IntSet.empty, IntSet.empty)]
        splits fitting required ((parts, identifier) : others) =
            concat
                [ [ ((parts : chosen, notChosen), narrowed, combined, IntSet.insert identifier chosenIds, notChosenIds)
                  | IntSet.null notChosenIds || IntSet.notMember identifier notChosenIds
                  , Just combined <- [meetTemplate remainingRequired (original (parts !! index))]
                  , let narrowed = fits remaining [parts !! index]
                  , not (null narrowed)
                  ]
                    <> [ ((chosen, parts : notChosen), remaining, remainingRequired, chosenIds, IntSet.insert identifier notChosenIds)
                       | IntSet.null chosenIds || IntSet.notMember identifier chosenIds
                       ]
                | ((chosen, notChosen), remaining, remainingRequired, chosenIds, notChosenIds) <- splits fitting required others
                ]
    -- The shapes whose root each of the parts fits.
    fits candidates parts = [(root, arity) | (root, arity) <- candidates, all (\part -> isJust (childParts part root (Arity arity))) parts]

{- | Intersect two finite structural templates. Nothing means that no term
matches both. A successful result matches exactly their conjunction.
Holes are independent wildcards. This check does not read an automaton or
interpret equality constraints or residual guards.
-}
meetTemplate :: (Eq symbol) => Template symbol -> Template symbol -> Maybe (Template symbol)
meetTemplate Hole right = Just right
meetTemplate left Hole = Just left
meetTemplate left right = do
    root <- case (leftRoot, rightRoot) of
        (Just first, Just second)
            | first /= second -> Nothing
        (Just first, _) -> Just (Just first)
        (_, other) -> Just other
    if (leftExact && leftCount < rightCount) || (rightExact && rightCount < leftCount)
        then Nothing
        else do
            children <-
                zipWithM
                    meetTemplate
                    (leftChildren <> replicate (count - leftCount) Hole)
                    (rightChildren <> replicate (count - rightCount) Hole)
            pure $ case (root, leftExact || rightExact) of
                (Nothing, True) -> AnyNode children
                (Just symbol, True) -> TemplateNode symbol children
                (Nothing, False) -> AnyPrefix children
                (Just symbol, False) -> TemplatePrefix symbol children
  where
    (leftRoot, leftExact, leftChildren) = parts left
    (rightRoot, rightExact, rightChildren) = parts right
    leftCount = length leftChildren
    rightCount = length rightChildren
    count = max leftCount rightCount
    parts Hole = (Nothing, False, [])
    parts (AnyNode children) = (Nothing, True, children)
    parts (TemplateNode symbol children) = (Just symbol, True, children)
    parts (AnyPrefix children) = (Nothing, False, children)
    parts (TemplatePrefix symbol children) = (Just symbol, False, children)

-- | Whether a template has no holes, so that it matches one term only.
ground :: Template symbol -> Bool
ground (TemplateNode _ children) = all ground children
ground _ = False

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
