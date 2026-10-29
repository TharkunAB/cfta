{- | Shared interned tree automata.

Every edge carries a 'Constraint': none for an ordinary automaton, path
equalities for an equality automaton, and a guard for a liquid automaton.
Each node and each edge has one identity. The operations are the same for
every symbol type.
-}
module Data.CFTA.Interned (
    -- * Nodes and edges
    Node (EmptyNode, InternedNode, InternedMu, InternedUnion, Rec, Node, Mu),
    Edge (InternedEdge, Edge),
    NodeId (..),
    EdgeId (..),
    RecNodeId (..),
    UninternedEdge (..),
    InternedNode (..),
    InternedMu (..),
    InternedUnion (..),
    IntersectId,
    pattern IntersectId,
    mkNode,
    mkEdge,
    emptyEdge,
    setChildren,
    modifyNode,
    createMu,
    createMuDontCleanup,
    createUnion,
    recursiveBoundary,
    substFree,
    edgeChildren,
    edgeConstraint,
    edgeSymbol,
    nodeIdentity,
    edgeIdentity,
    numNestedMu,
    freeVars,
    module Data.CFTA.Constraint,

    -- * Operations
    nodeMapChildren,
    mapNodes,
    crush,
    unfoldOuterRec,
    refold,
    refoldEdges,
    nodeEdges,
    unfoldBounded,
    boundDepth,
    nodeCount,
    edgeCount,
    union,
    intersect,
    intersectEdge,
    withoutRedundantEdges,
    dropEdgeConstraints,
    dropConstraints,
    acceptsWith,
    fixUnbounded,
    fixWithin,
    pathsMatching,
    requirePath,

    -- * Views and conversion
    InternedState (..),
    FTAViewError (..),
    toFTA,
    canonicalFTA,
    toRows,
    stateOf,
    fromFTA,
    fromRows,
    ViewPath,
    ViewStep (..),
    StateView (..),
    toTree,
    reachable,
    canonicalClasses,
) where

import Control.Monad.State.Strict (State, evalState, gets, modify')
import Data.Graph (flattenSCC, stronglyConnComp)
import Data.Hashable (Hashable)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import Data.List (sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import Type.Reflection (Typeable)

import Data.CFTA (StateView (..), ViewPath, ViewStep (..))
import qualified Data.CFTA as FTA
import Data.CFTA.Constraint
import Data.CFTA.Internal.Tree (toTreeBy, trimRows)
import Data.CFTA.Interned.Operations
import Data.CFTA.Interned.Type

-- | State identity in the explicit view of an interned automaton.
data InternedState = EmptyState | InternedState !NodeId
    deriving (Eq, Ord, Show)

-- | Failure while exposing an interned graph as an explicit-state automaton.
data FTAViewError
    = -- | A recursive variable is free in the root node.
      OpenNode
    deriving (Eq, Show)

{- | Expose the shared graph with its constraints unchanged.

Each interned node becomes one state. The operation does not enumerate terms
or interpret transition constraints. Use the explicit-state interface when
an operation must retain caller-supplied state names. The rows are those of
'toRows'. A symbol can occur at several arities. The names of the states depend
on the identities of the nodes in this process; 'canonicalFTA' gives names that
depend on the content of the graph only.
-}
toFTA ::
    (Hashable symbol, Typeable symbol) =>
    Node symbol ->
    Either FTAViewError (FTA.FTA InternedState symbol Constraint)
toFTA root
    | not (Set.null $ freeVars root) = Left OpenNode
    | otherwise =
        either (const $ error "cfta bug in Data.CFTA.Interned.toFTA: the rows of a closed node are not closed") Right $
            FTA.mkFTA (stateOf root) (Map.toList $ toRows root)

{- | The explicit graph of a closed node, with names that depend on the content
of the graph only. Each state is a canonical class ('canonicalClasses') of the
nodes that the root reaches, and the initial state is the class of the root.
A row has the transitions of one node of its class, in the order of their
arity, symbol, child states, and constraint; equal transitions are kept once.
The nodes of one class have the same language, so the graph has the language of
the node. The same node, built in any order and in any process, gives the same
graph, so the text of the graph can identify the language.
-}
canonicalFTA ::
    (Hashable symbol, Ord symbol, Typeable symbol) =>
    Node symbol ->
    Either FTAViewError (FTA.FTA Int symbol Constraint)
canonicalFTA root
    | not (Set.null $ freeVars root) = Left OpenNode
    | otherwise =
        either (const $ error "cfta bug in Data.CFTA.Interned.canonicalFTA: the rows of a closed node are not closed") Right $
            FTA.mkFTA initial (if IntMap.null graph then [(initial, [])] else rows)
  where
    graph = reachable root
    classes = canonicalClasses $ IntMap.map (map $ \edge -> (shape edge, map nodeIdentity $ edgeChildren edge)) graph
    classOf node = let NodeId ident = nodeIdentity node in classes IntMap.! ident
    initial = if IntMap.null graph then 0 else classOf root
    shape edge = (length $ edgeChildren edge, edgeSymbol edge, constraintEqualities constraint, constraintGuard constraint)
      where
        constraint = edgeConstraint edge
    transition edge = FTA.Transition (edgeSymbol edge) (map classOf $ edgeChildren edge) (edgeConstraint edge)
    row edges = Map.elems $ Map.fromList [((shape edge, FTA.transitionChildren (transition edge)), transition edge) | edge <- edges]
    rows = Map.toList $ Map.fromList [(classes IntMap.! ident, row edges) | (ident, edges) <- IntMap.toList graph]

{- | The transitions of each node that a closed interned graph reaches, keyed by
the state of the node, with their constraints unchanged.

This is the one adapter from interned nodes to explicit rows: 'toFTA' checks
these rows, and the count table of the generators reads them directly. The
initial state is 'stateOf' the root.
-}
toRows ::
    (Hashable symbol, Typeable symbol) =>
    Node symbol ->
    Map.Map InternedState [FTA.Transition InternedState symbol Constraint]
toRows EmptyNode = Map.singleton EmptyState []
toRows root =
    Map.fromDistinctAscList
        [(InternedState (NodeId ident), map transition edges) | (ident, edges) <- IntMap.toList (reachable root)]
  where
    transition edge =
        FTA.Transition
            (edgeSymbol edge)
            (map stateOf $ edgeChildren edge)
            (edgeConstraint edge)

{- | Expose typed state and transition labels for a closed interned grammar.

The view retains the original nodes, edges, and constraints. Recursive and
shared references use the same finite representation as 'FTA.toTree'. Open
roots return 'OpenNode'.
-}
toTree ::
    (Hashable symbol, Typeable symbol) =>
    Node symbol ->
    Either FTAViewError (Tree.Tree (Either (StateView (Node symbol)) (Edge symbol)))
toTree root
    | not (Set.null $ freeVars root) = Left OpenNode
    | otherwise = Right $ toTreeBy nodeEdges edgeChildren root

-- TODO: Data.Graph.reachable says what this function does, but it needs the
-- graph first, and this walk is what finds the graph. The other searches that
-- discover their states as they go (Refinement.Automaton.located,
-- Internal.Tree.explore, Simple.intersect) stay hand written for the same
-- reason.

{- | Outgoing alternatives of every node reachable from a root. The key is the
'Int' of the 'NodeId' of the node. An empty root reaches no node.
-}
reachable ::
    (Hashable symbol, Typeable symbol) =>
    Node symbol -> IntMap [Edge symbol]
reachable root = collect IntMap.empty [root]
  where
    collect seen [] = seen
    collect seen (EmptyNode : pending) = collect seen pending
    collect seen (node : pending)
        | IntMap.member ident seen = collect seen pending
        | otherwise = collect (IntMap.insert ident edges seen) (concatMap edgeChildren edges <> pending)
      where
        NodeId ident = nodeIdentity node
        edges = nodeEdges node

{- | Canonical classes for the nodes of a graph, which can have cycles.

A node is a list of edges, and an edge is a key and the identities of its
children. The graph and the result use the 'Int' of a 'NodeId' as the key.
Every node starts in one class. Each round keys a node by its class
and the sorted keys of its edges with the classes of their children, and
numbers the classes in the order of those keys. The rounds stop when no class
splits (ordered partition refinement). The classes depend on the content of
the graph only, not on the identities of its nodes. A node keeps its class
first in its key, so two nodes keep their order once a round separates them,
and the order of two nodes does not depend on the rest of the graph. Two
nodes share a class when their edges are the same up to the classes of their
children.
-}
canonicalClasses :: (Ord key) => IntMap.IntMap [(key, [NodeId])] -> IntMap.IntMap Int
canonicalClasses graph = refine (IntMap.map (const 0) graph) (min 1 $ IntMap.size graph)
  where
    refine classes count
        | count' == count = classes'
        | otherwise = refine classes' count'
      where
        keys =
            IntMap.mapWithKey
                ( \nodeId edges ->
                    (classes IntMap.! nodeId, sort [(key, [classes IntMap.! child | NodeId child <- children]) | (key, children) <- edges])
                )
                graph
        numbers = Map.fromList $ zip (Set.toAscList $ Set.fromList $ IntMap.elems keys) [0 ..]
        classes' = IntMap.map (numbers Map.!) keys
        count' = Map.size numbers

{- | Intern an explicit-state graph without interpreting constraints.

The graph is trimmed first. Each reachable state becomes one node. A state on
a cycle becomes a 'Mu' whose body refers back to it through 'Rec', so a
recursive graph imports without a bound. The states of each strongly
connected component get one order: the order in which a depth-first walk
from the initial state first meets them. The binders on a path nest in that
order. Inside a 'Mu', a state that an enclosing 'Mu' binds refers to that
binder. Another state of the component is built under the enclosing binders
of the states before it only, and it binds the later states again where it
needs them. A state becomes a 'Mu' only when its body refers to it. Thus a
node is built once for each set of enclosing binders, and a component of k
states has at most 2^k of them. (When the binders nested in the order in
which each path met them, the result could have about e * (k - 1)!.)
Constraint layers can annotate the source before this conversion.
-}
fromFTA ::
    (Ord state, Hashable symbol, Typeable symbol) =>
    FTA.FTA state symbol Constraint -> Node symbol
fromFTA graph = fromRows (FTA.initialState graph) (FTA.transitionTable graph)

{- | 'fromFTA' on the transitions of each state and an initial state. The
symbols need no consistent arity, as for 'toRows'.
-}
fromRows ::
    forall state symbol.
    (Ord state, Hashable symbol, Typeable symbol) =>
    state -> Map.Map state [FTA.Transition state symbol Constraint] -> Node symbol
fromRows initial rows = evalState (build IntSet.empty 0) Map.empty
  where
    -- The rows that the initial state reaches and that accept a term, as
    -- 'FTA.trim' keeps them.
    trimmed = Map.insertWith (\_ kept -> kept) initial [] (trimRows FTA.transitionChildren (Map.toList rows) initial)
    successors state = concatMap FTA.transitionChildren (Map.findWithDefault [] state trimmed)

    -- Each state is its position in the order in which a depth-first walk
    -- from the initial state first meets it. The initial state is 0, and the
    -- binders of a component nest in this order. A position is also the
    -- reference to the binder of its state.
    order = walk Set.empty [initial]
    walk _ [] = []
    walk seen (state : pending)
        | Set.member state seen = walk seen pending
        | otherwise = state : walk (Set.insert state seen) (successors state <> pending)
    position = Map.fromList $ zip order [0 :: Int ..]
    transitionsAt =
        IntMap.fromList
            [ ( position Map.! state
              , [ (transition, map (position Map.!) (FTA.transitionChildren transition))
                | transition <- Map.findWithDefault [] state trimmed
                ]
              )
            | state <- order
            ]
    components = map flattenSCC (stronglyConnComp [(here, here, concatMap snd edges) | (here, edges) <- IntMap.toList transitionsAt])
    component = IntMap.fromList [(here, index) | (index, members) <- zip [0 :: Int ..] components, here <- members]

    -- Build the node of a state under binders for the given states of its
    -- component, which all come before it, and remember it for these states.
    -- One table serves the whole graph, so a node that two parents or two
    -- entries of a component need is built once. The body is built once,
    -- with a reference to the state, and 'createMu' substitutes for the
    -- reference: 'createMu' applies its function more than once, and building
    -- the body for each application would build the nested binders again. A
    -- state whose body does not refer to it gets no binder.
    build :: IntSet.IntSet -> Int -> State (Map.Map (IntSet.IntSet, Int) (Node symbol)) (Node symbol)
    build bound here = do
        known <- gets (Map.lookup (bound, here))
        case known of
            Just node -> pure node
            Nothing -> do
                open <- body (IntSet.insert here bound) here
                let node
                        | Set.member (RecState here) (freeVars open) = createMu $ \self -> substFree (RecState here) self open
                        | otherwise = open
                modify' (Map.insert (bound, here) node)
                pure node

    -- A child in another component cannot reach a bound state, so it is built
    -- under no binder. A bound child is the reference of its binder. Another
    -- child is built under the binders of the states before it, so the
    -- binders on every path nest in the order.
    body bound here = mkNode <$> mapM edge (transitionsAt IntMap.! here)
      where
        edge (transition, children) =
            (\nodes -> mkEdge (FTA.transitionSymbol transition) nodes (FTA.transitionConstraint transition))
                <$> mapM child children
        child next
            | component IntMap.! next /= component IntMap.! here = build IntSet.empty next
            | IntSet.member next bound = pure (Rec (RecState next))
            | otherwise = build (fst (IntSet.split next bound)) next

-- | Name the empty state or read the shared canonical identity.
stateOf :: Node symbol -> InternedState
stateOf EmptyNode = EmptyState
stateOf node = InternedState (nodeIdentity node)
