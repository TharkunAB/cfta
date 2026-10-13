{-# OPTIONS_GHC -Wno-orphans #-}

-- | Constraint-independent operations on shared interned automata.
module Data.CFTA.Interned.Operations (
    nodeMapChildren,
    mapNodes,
    crush,
    unfoldOuterRec,
    refold,
    nodeEdges,
    unfoldBounded,
    boundDepth,
    nodeCount,
    edgeCount,
    union,
    acceptsWith,
    dropEdgeConstraints,
    dropConstraints,
    intersect,
    mergeAlternatives,
    withoutRedundantEdges,
    intersectEdge,
    fixUnbounded,
    fixWithin,
    pathsMatching,
    requirePath,
) where

import Control.Monad.State.Strict (State, evalState, get, modify')
import Data.Coerce (coerce)
import Data.Containers.ListUtils (nubOrd)
import Data.Functor.Identity (Identity (..))
import qualified Data.HashMap.Lazy as HashMap
import Data.Hashable (Hashable (..))
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (compareLength, partition, transpose, (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Monoid (Sum (..))
import Data.Set (Set)
import qualified Data.Set as Set
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (Typeable)

import Data.CFTA.Constraint (Constraint (..), conjoinConstraints, noConstraint)
import Data.CFTA.Index (Depth (..))
import Data.CFTA.Internal.Tree (acceptsBy, adjustAt)
import Data.CFTA.Interned.Cache (CacheFamily, freshCacheWith, intern, newCacheFamily, newIdSupply, selectCache)
import Data.CFTA.Interned.FlatMemo (FlatMemoCache, memoFlatTypeableWith, newFlatMemoCache)
import Data.CFTA.Interned.Memo
import Data.CFTA.Interned.Type
import Data.CFTA.Path (ChildIndex (..), Path (ConsPath, EmptyPath), Pathable (..))
import Data.CFTA.Term (Term)

-- | Transform the immediate alternatives of one node.
{-# INLINEABLE nodeMapChildren #-}
nodeMapChildren ::
    (Hashable symbol, Typeable symbol) =>
    (Edge symbol -> Edge symbol) -> Node symbol -> Node symbol
nodeMapChildren _ EmptyNode = EmptyNode
nodeMapChildren f n@(Mu _) = nodeMapChildren f (unfoldOuterRec n)
nodeMapChildren f (Node es) = Node (map f es)
nodeMapChildren f node@(InternedUnion _) = Node (map f $ nodeEdges node)
nodeMapChildren _ (Rec _) = error "nodeMapChildren: unexpected Rec"

{- | Transform each reachable node. Memoize separately for each transformation.

Under a 'Mu', the body is rebuilt three times with different placeholders, so
the function also receives 'Rec' nodes that hold 'RecDepth' and 'RecUnint'.
Return such nodes unchanged.
-}
{-# INLINEABLE mapNodes #-}
mapNodes ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    (Node symbol -> Node symbol) -> Node symbol -> Node symbol
mapNodes f = go
  where
    -- This table belongs to this transformation.
    go :: Node symbol -> Node symbol
    go = memo (mapNodesStep go f)
    {-# NOINLINE go #-}

-- | Perform one recursive traversal step using the supplied recursive call.
{-# INLINEABLE mapNodesStep #-}
mapNodesStep ::
    (Hashable symbol, Typeable symbol) =>
    (Node symbol -> Node symbol) ->
    (Node symbol -> Node symbol) ->
    Node symbol ->
    Node symbol
mapNodesStep _ _ EmptyNode = EmptyNode
mapNodesStep recurse f (Node es) =
    f $ Node $ map (\edge -> setChildren edge (map recurse (edgeChildren edge))) es
mapNodesStep recurse f (Mu body) = f $ Mu (recurse . body)
mapNodesStep recurse f (InternedUnion alternatives) = f $ createUnion $ map recurse $ internedUnionMembers alternatives
mapNodesStep _ f (Rec recId) = f $ Rec recId

{- | Fold over all reachable nodes, visiting each shared node once.

This name originates from the @crush@ operator in the Stratego language.
Although @m@ is only constrained to be a monoid, this function makes no
guarantees about traversal order. Recursive nodes and ordinary nodes draw
identities from one counter, so one visited set covers both.
-}
{-# INLINEABLE crush #-}
crush :: forall symbol m. (Monoid m) => (Node symbol -> m) -> Node symbol -> m
crush f = \n -> evalState (go n) IntSet.empty
  where
    go :: Node symbol -> State IntSet m
    go EmptyNode = return mempty
    go (Rec _) = return mempty
    go n = do
        seen <- get
        let NodeId nId = nodeIdentity n
        if IntSet.member nId seen
            then return mempty
            else do
                modify' (IntSet.insert nId)
                mappend (f n) . mconcat <$> mapM go (children n)

    children (InternedMu mu) = [internedMuBody mu]
    children (InternedNode node) = [child | edge <- internedNodeEdges node, child <- edgeChildren edge]
    children (InternedUnion alternatives) = internedUnionMembers alternatives
    children _ = []

-- | Run a fold function only on normal non-recursive nodes.
{-# INLINEABLE onNormalNodes #-}
onNormalNodes :: forall symbol m. (Monoid m) => (Node symbol -> m) -> Node symbol -> m
onNormalNodes f n@(InternedNode _) = f n
onNormalNodes _ _ = mempty

-- Folding

-- | Tables for the unfolding of recursive nodes.
unfoldOuterRecCache :: TypeableMemoCache
unfoldOuterRecCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE unfoldOuterRecCache #-}

-- | Unfold one outer 'Mu' layer. The unfolding of each recursive node is shared.
unfoldOuterRec ::
    forall symbol.
    (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol
unfoldOuterRec = memoTypeableWith @symbol unfoldOuterRecCache go
  where
    go n@(Mu x) = x n
    go _ = error "unfoldOuterRec: Must be called on a Mu node"

{- | Outgoing alternatives after finite closure of recursive and union references.

An ordinary node and a 'Mu' that unfolds to one give their edges directly.
Other nodes take the closure through unfoldings and union operands. An open
union must be bound before this view can expose its alternatives. An
unresolved union reference is an error, not an empty language.
-}
{-# INLINEABLE nodeEdges #-}
nodeEdges ::
    (Hashable symbol, Typeable symbol) => Node symbol -> [Edge symbol]
nodeEdges (InternedNode node) = internedNodeEdges node
nodeEdges EmptyNode = []
nodeEdges (Rec _) = []
nodeEdges node@(InternedMu _)
    | InternedNode unfolded <- unfoldOuterRec node = internedNodeEdges unfolded
nodeEdges root = Set.toList $ Set.fromList $ collect IntSet.empty [root]
  where
    collect _ [] = []
    collect seen (EmptyNode : rest) = collect seen rest
    collect _ (Rec reference : _) = error $ "nodeEdges: unresolved union reference " <> show reference
    collect seen (InternedNode node : rest) = internedNodeEdges node ++ collect seen rest
    collect seen (node : rest)
        | IntSet.member ident seen = collect seen rest
        | otherwise = collect (IntSet.insert ident seen) (members node ++ rest)
      where
        NodeId ident = nodeIdentity node

    members node@(InternedMu _) = [unfoldOuterRec node]
    members (InternedUnion alternatives) = internedUnionMembers alternatives
    members _ = []

-- | Tables for recursive refolding.
genericRefoldCache :: TypeableMemoCache
genericRefoldCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericRefoldCache #-}

-- | Replace repeated unfoldings with recursive nodes where possible.
{-# INLINEABLE refold #-}
refold ::
    forall symbol.
    (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol
refold node = memoTypeableWith @symbol genericRefoldCache go node
  where
    go :: Node symbol -> Node symbol
    go n =
        if HashMap.null muNodeMap
            then n
            else fixUnbounded (mapNodes tryUnfold) n
      where
        muNodeMap =
            crush
                ( \case
                    x@(Mu _) -> HashMap.singleton (unfoldOuterRec x) x
                    _ -> HashMap.empty
                )
                n

        tryUnfold x = fromMaybe x (HashMap.lookup x muNodeMap)

{- | Unfold recursive nodes at most the given number of rounds.

A bound of zero or less unfolds nothing and replaces every 'Mu' with
'EmptyNode', leaving only the terms that need no recursion at all. Matching
@0@ alone would leave a negative bound counting down forever.
-}
{-# INLINEABLE unfoldBounded #-}
unfoldBounded ::
    (Hashable symbol, Typeable symbol) => Int -> Node symbol -> Node symbol
unfoldBounded rounds
    | rounds <= 0 =
        mapNodes
            ( \case
                Mu _ -> EmptyNode
                n -> n
            )
    | otherwise =
        unfoldBounded (rounds - 1)
            . mapNodes
                ( \case
                    n@(Mu _) -> unfoldOuterRec n
                    n -> n
                )

-- Size operations

{- | Retain terms whose leaves are at most the given depth from the root.

A leaf has depth zero. A recursive node unfolds until the depth is spent, so
the result is finite for a cyclic input, and a negative depth is the empty
language. Symbols and constraints remain unchanged. The order of alternatives
can change. A node lists its alternatives in the order of their identities,
and a bounded alternative is a new edge with a new identity.
-}
boundDepth ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    Depth -> Node symbol -> Node symbol
boundDepth maximumDepth root = evalState (go maximumDepth root) Map.empty
  where
    go :: Depth -> Node symbol -> State (Map.Map (Depth, NodeId) (Node symbol)) (Node symbol)
    go _ EmptyNode = pure EmptyNode
    go _ (Rec _) = error "boundDepth: unexpected Rec"
    go remaining node
        | remaining < 0 = pure EmptyNode
        | otherwise = do
            known <- get
            case Map.lookup (remaining, nodeIdentity node) known of
                Just bounded -> pure bounded
                Nothing -> do
                    bounded <- Node <$> traverse edge (filter (\e -> remaining > 0 || null (edgeChildren e)) (nodeEdges node))
                    modify' (Map.insert (remaining, nodeIdentity node) bounded)
                    pure bounded
      where
        edge e = setChildren e <$> traverse (go (remaining - 1)) (edgeChildren e)

-- | Count reachable non-recursive nodes, sharing-aware.
{-# INLINEABLE nodeCount #-}
nodeCount :: Node symbol -> Int
nodeCount = getSum . crush (onNormalNodes $ const $ Sum 1)

-- | Count reachable outgoing edges, sharing-aware.
{-# INLINEABLE edgeCount #-}
edgeCount :: Node symbol -> Int
edgeCount = getSum . crush (onNormalNodes go)
  where
    go (InternedNode node) = Sum (length (internedNodeEdges node))
    go _ = mempty

-- | Replace the edge constraint with the unconstrained value.
{-# INLINEABLE dropEdgeConstraints #-}
dropEdgeConstraints ::
    (Hashable symbol, Typeable symbol) => Edge symbol -> Edge symbol
dropEdgeConstraints e = Edge (edgeSymbol e) (edgeChildren e)

-- | Tables for constraint removal.
genericDropConstraintsCache :: TypeableMemoCache
genericDropConstraintsCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericDropConstraintsCache #-}

-- | Remove every edge constraint. This can broaden the accepted language.
{-# INLINEABLE dropConstraints #-}
dropConstraints ::
    forall symbol.
    (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol
dropConstraints node = memoTypeableWith @symbol genericDropConstraintsCache go node
  where
    go = mapNodesStep dropConstraints dropNodeConstraints
      where
        dropNodeConstraints (Node es) = Node (map dropEdgeConstraints es)
        dropNodeConstraints n = n

-- Intersect

{- | Remove edges that are subsumed by another edge with the same symbol.

The input is the alternative list of a node, which is already free of
duplicates. The comparison order within a symbol group follows the input.
-}
{-# INLINEABLE dropRedundantEdges #-}
dropRedundantEdges ::
    forall symbol.
    (Hashable symbol, Typeable symbol) => [Edge symbol] -> [Edge symbol]
dropRedundantEdges origEs = concatMap reduceCluster clusters
  where
    clusters = clusterByHash edgeSymbol origEs

    reduceCluster :: [Edge symbol] -> [Edge symbol]
    reduceCluster [] = []
    reduceCluster (e : es) = case ruleOut e es of
        -- Optimization: If e' > e, likely to be greater than other things;
        -- move it to front and rule out more edges next iteration.
        --
        -- No noticeable difference in overall wall clock time (7/2/21),
        -- but a few % reduction in calls to intersectEdgeSameSymbol. That
        -- measurement came from the ECTA engine. On the CFTA engine, without
        -- the move, the instruction counts of micro-bench and of the generator
        -- benchmark cells change by less than 0.001%.
        (Just e', es') -> reduceCluster (e' : es')
        (Nothing, es') -> e : reduceCluster es'

    -- Drop the alternatives that @e@ accepts, or report one that accepts @e@.
    ruleOut ::
        Edge symbol -> [Edge symbol] -> (Maybe (Edge symbol), [Edge symbol])
    ruleOut _ [] = (Nothing, [])
    ruleOut e (x : xs)
        | common == x = ruleOut e xs
        | common == e = (Just x, xs)
        | otherwise = let (res, notRuledOut) = ruleOut e xs in (res, x : notRuledOut)
      where
        common = intersectEdgeSameSymbol e x

-- | Intersect two edges when they have the same symbol.
{-# INLINEABLE intersectEdge #-}
intersectEdge ::
    (Hashable symbol, Typeable symbol) =>
    Edge symbol -> Edge symbol -> Maybe (Edge symbol)
intersectEdge e1 e2
    | edgeSymbol e1 /= edgeSymbol e2 = Nothing
    | length (edgeChildren e1) /= length (edgeChildren e2) = Nothing
    | otherwise = Just $ intersectEdgeSameSymbol e1 e2

-- | Tables for intersection of edges with the same symbol.
genericIntersectEdgeSameSymbolCache :: TypeableMemoCache
genericIntersectEdgeSameSymbolCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericIntersectEdgeSameSymbolCache #-}

-- | Intersect edges with equal symbols and reject unequal arities.
intersectEdgeSameSymbol ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    Edge symbol -> Edge symbol -> Edge symbol
intersectEdgeSameSymbol left right =
    memo2TypeableWith @symbol genericIntersectEdgeSameSymbolCache go left right
  where
    go e1 e2
        | e2 < e1 = intersectEdgeSameSymbol e2 e1
        | length (edgeChildren e1) /= length (edgeChildren e2) = emptyEdge (edgeSymbol e1)
        | otherwise =
            mkEdge
                (edgeSymbol e1)
                (zipWith intersect (edgeChildren e1) (edgeChildren e2))
                (edgeConstraint e1 `conjoinConstraints` edgeConstraint e2)
{-# INLINEABLE intersectEdgeSameSymbol #-}

-- | Intersection of two automata.
intersect ::
    (Hashable symbol, Typeable symbol) =>
    Node symbol -> Node symbol -> Node symbol
intersect l r = intersectOpen (emptyIntersectionDom, l, r)
{-# INLINEABLE intersect #-}

-- Intersection internals

{- | Intersection domain

Information required to compute the intersection of open terms.
-}
data IntersectionDom symbol = ID
    { idFree :: IntMap (Node symbol)
    -- ^ Value of all free variables inside the term, by the 'NodeId' of their 'Mu' (so that we can unfold when necessary)
    , idRecInt :: Set IntersectId
    -- ^ Intersection problems we encountered previously (to avoid infinite unrolling)
    , idIdent :: !Int
    -- ^ The identity of the domain: equal domains have one identity.
    }

instance Eq (IntersectionDom symbol) where
    left == right = idIdent left == idIdent right

instance Hashable (IntersectionDom symbol) where
    hashWithSalt s dom = hashWithSalt s (idIdent dom)

-- | Tables that give equal intersection domains one identity.
genericIntersectionDomCache :: CacheFamily
genericIntersectionDomCache = unsafePerformIO newCacheFamily
{-# NOINLINE genericIntersectionDomCache #-}

{- | Build a domain, interned. Both containers list their elements in key order, a canonical form.

The empty domain is 'emptyIntersectionDom'. Every other domain gets the
identity from its cache plus one, so no domain shares the identity of the
empty domain.
-}
{-# INLINEABLE mkIntersectionDom #-}
mkIntersectionDom ::
    forall symbol. (Typeable symbol) => IntMap (Node symbol) -> Set IntersectId -> IntersectionDom symbol
mkIntersectionDom free recInt
    | IntMap.null free, Set.null recInt = emptyIntersectionDom
    | otherwise =
        intern
            (selectCache @symbol genericIntersectionDomCache (newIdSupply >>= freshCacheWith))
            (\identity _ -> ID free recInt (identity + 1))
            (IntMap.toList free, Set.toList recInt)

{- | An intersection environment with no free or pending variables.

Its identity is 0. It is one constant for all symbol types, so each top-level
'intersect' uses it without a lookup.
-}
emptyIntersectionDom :: IntersectionDom symbol
emptyIntersectionDom = ID IntMap.empty Set.empty 0

{- | Tables for node intersection in a recursive environment. The key is the
identity of the domain and the memo keys of the two nodes.
-}
genericIntersectOpenCache :: FlatMemoCache
genericIntersectOpenCache = unsafePerformIO newFlatMemoCache
{-# NOINLINE genericIntersectOpenCache #-}

{- | Intersect two nodes under the same recursive environment.

A node without a memo key is a placeholder. The intersection does not
memoize a pair with a placeholder.
-}
intersectOpen ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    (IntersectionDom symbol, Node symbol, Node symbol) -> Node symbol
{-# INLINEABLE intersectOpen #-}
intersectOpen (domain, left, right) =
    case (nodeMemoKey left, nodeMemoKey right) of
        (Just leftKey, Just rightKey) ->
            memoFlatTypeableWith @symbol genericIntersectOpenCache (idIdent domain) leftKey rightKey (onNode domain left right)
        _ -> onNode domain left right
  where
    onNode ::
        IntersectionDom symbol -> Node symbol -> Node symbol -> Node symbol
    onNode !dom l r =
        case (l, r) of
            -- Rule out empty cases first
            -- This justifies the use of nodeIdentity (@i@, @j@) for the other cases
            (EmptyNode, _) -> EmptyNode
            (_, EmptyNode) -> EmptyNode
            -- For closed terms, improve memoization performance by using the empty environment
            _ | Set.null (freeVars l), Set.null (freeVars r), not (IntMap.null (idFree dom)) -> l `intersect` r
            -- Special case for self-intersection (equality check is cheap of course: just uses the interned 'NodeId')
            _ | l == r, Set.null (freeVars l) -> l
            -- Always intersect nodes in the same order. This is important for two reasons:
            --
            -- 1. It will increase the probability of a cache hit (i.e., improve memoization)
            -- 2. It will increase the probability of being able to use 'idRecInt'
            _ | l > r -> intersectOpen (dom, r, l)
            -- If we have seen this exact problem before, refer to enclosing Mu.
            _ | Set.member (IntersectId i j) (idRecInt dom) -> Rec (RecIntersect (IntersectId i j))
            -- When encountering a 'Mu', extend the domain appropriately.
            (InternedMu l', InternedMu r') -> maybeMu $ intersectOpen (extendEnv [(i, l), (j, r)], internedMuBody l', internedMuBody r')
            (InternedMu l', _) -> maybeMu $ intersectOpen (extendEnv [(i, l)], internedMuBody l', r)
            (_, InternedMu r') -> maybeMu $ intersectOpen (extendEnv [(j, r)], l, internedMuBody r')
            (InternedUnion alternatives, _) -> createUnion [intersectOpen (dom, member, r) | member <- internedUnionMembers alternatives]
            (_, InternedUnion alternatives) -> createUnion [intersectOpen (dom, l, member) | member <- internedUnionMembers alternatives]
            -- When encountering a free variable, look up the corresponding value in the environment.
            -- (Recall that already-seen intersection problems are handled above.)
            (Rec l', _) -> intersectOpen (dom, findFreeVar l', r)
            (_, Rec r') -> intersectOpen (dom, l, findFreeVar r')
            -- Finally, the real intersection work happens here
            (InternedNode l', InternedNode r') ->
                Node $
                    hashJoin
                        edgeSymbol
                        (\e e' -> intersectOpenEdge (dom, e, e'))
                        (internedNodeEdges l')
                        (internedNodeEdges r')
      where
        -- Node identities (should only be used (forced) if previously established the nodes are not empty)
        i, j :: NodeId
        i = nodeIdentity l
        j = nodeIdentity r

        -- Extend domain when we encounter a 'Mu'
        -- We might see one or two 'Mu's (if we happen to see a 'Mu' on both sides at once)
        extendEnv :: [(NodeId, Node symbol)] -> IntersectionDom symbol
        extendEnv bindings =
            mkIntersectionDom
                (IntMap.union (IntMap.fromList (coerce bindings)) (idFree dom))
                (Set.insert (IntersectId i j) (idRecInt dom))

        -- Find value of free variables in the terms
        -- Since we assume the input terms are fully interned, we only deal with 'RecInt'.
        findFreeVar :: RecNodeId -> Node symbol
        findFreeVar (RecInt (NodeId intId)) | Just n <- IntMap.lookup intId (idFree dom) = n
        findFreeVar recId = error $ "findFreeVar: unexpected " <> show recId

        -- We only insert a 'Mu' node when necessary.
        maybeMu :: Node symbol -> Node symbol
        maybeMu n
            | RecIntersect (IntersectId i j) `Set.member` freeVars n =
                Mu $ \recNode -> substFree (RecIntersect (IntersectId i j)) recNode n
            | otherwise =
                n

{- | Tables for edge intersection in a recursive environment. The key is the
identities of the domain and of the two edges.
-}
genericIntersectOpenEdgeCache :: FlatMemoCache
genericIntersectOpenEdgeCache = unsafePerformIO newFlatMemoCache
{-# NOINLINE genericIntersectOpenEdgeCache #-}

-- | Intersect two edges under the same recursive environment.
intersectOpenEdge ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    (IntersectionDom symbol, Edge symbol, Edge symbol) -> Edge symbol
{-# INLINEABLE intersectOpenEdge #-}
intersectOpenEdge (domain, left, right) =
    memoFlatTypeableWith @symbol
        genericIntersectOpenEdgeCache
        (idIdent domain)
        (coerce (edgeId left))
        (coerce (edgeId right))
        (onEdge domain left right)
  where
    onEdge ::
        IntersectionDom symbol -> Edge symbol -> Edge symbol -> Edge symbol
    onEdge _ l r | length (edgeChildren l) /= length (edgeChildren r) = emptyEdge (edgeSymbol l)
    onEdge !dom l r =
        mkEdge
            (edgeSymbol l)
            (zipWith (\a b -> intersectOpen (dom, a, b)) (edgeChildren l) (edgeChildren r))
            (edgeConstraint l `conjoinConstraints` edgeConstraint r)

-- Union

-- | Tables for 'mergeAlternatives'.
genericMergeAlternativesCache :: TypeableMemoCache
genericMergeAlternativesCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericMergeAlternativesCache #-}

{- | Merge the alternatives of a closed ordinary node. The result accepts
every term of the given node and possibly more.

When more than four edges have one symbol and number of children, they become
one edge, whose children are the unions of their children. Smaller groups stay
as they are. The merge goes on into the children. An edge that stays keeps its
constraint. A merged edge has no constraint, so it can accept more terms at any
arity; with more than one child it can also take each child from a different
edge. A recursive node, a union node, and a reference stay as they are. A child
union that contains a recursive or union node is not merged further.

At a merged ordinary node there are at most four edges for each symbol and
number of children, so an intersection pairs each edge of the other node with at
most four edges instead of all matching alternatives. This bound does not apply
below the recursive and union boundaries. A small group stays exact because a
merge keeps more terms, and the reduction then narrows less: a narrower
automaton is faster to enumerate.

The merge is an over-approximation, not an exact transformation. Its one
caller, the narrowing set of 'Data.CFTA.Equality.Operations.reduceEqConstraints',
keeps the language, because enumeration and 'accepts' still check each
equality class.
-}
mergeAlternatives :: forall symbol. (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol
{-# INLINEABLE mergeAlternatives #-}
mergeAlternatives = memoTypeableWith @symbol genericMergeAlternativesCache go
  where
    go node@(InternedNode payload)
        | null (freeVars node) =
            Node
                [ merged
                | group <- HashMap.elems groups
                , merged <- case group of
                    edge : _
                        | not (null (drop smallGroup group)) ->
                            [Edge (edgeSymbol edge) (map mergedUnion (transpose (map edgeChildren group)))]
                    _ -> [setChildren edge (map mergeAlternatives (edgeChildren edge)) | edge <- group]
                ]
      where
        groups =
            HashMap.fromListWith
                (flip (<>))
                [((edgeSymbol edge, length (edgeChildren edge)), [edge]) | edge <- internedNodeEdges payload]
    go node = node

    -- A group of at most this many edges stays exact: its product costs little.
    smallGroup = 4

    -- The union of the children at one position. A recursive node among them
    -- stays a recursive node, and the children that it accepts go. Do not
    -- merge a union of recursive boundaries: unfolding it can request the
    -- same child union again.
    mergedUnion children = case nubOrd kept of
        [single] -> single
        others
            | any recursiveBoundary others -> union others
            | otherwise -> mergeAlternatives (union others)
      where
        recursive = [child | child@(InternedMu _) <- children, null (freeVars child)]
        kept = [child | child <- children, child `elem` recursive || not (any (`accepts` child) recursive)]
        accepts big small = null (freeVars small) && subsumes big small

{- | Whether the first closed node accepts every term of the second. The test
is structural and can answer no for a node that does accept every term: an
edge of the first node must have the symbol of an edge of the second, no
constraint, and children that accept the children of that edge. A pair that
the test meets again below itself counts as accepted, as for the greatest
fixed point of the recursive nodes.
-}
subsumes :: forall symbol. (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol -> Bool
subsumes = go Set.empty
  where
    go :: Set (NodeId, NodeId) -> Node symbol -> Node symbol -> Bool
    go _ _ EmptyNode = True
    go _ EmptyNode _ = False
    go above b s
        | b == s = True
        | Set.member pair above = True
        | otherwise = all (\edge -> any (covers (Set.insert pair above) edge) (nodeEdges b)) (nodeEdges s)
      where
        pair = (nodeIdentity b, nodeIdentity s)
    covers above narrow wide =
        edgeSymbol wide == edgeSymbol narrow
            && length (edgeChildren wide) == length (edgeChildren narrow)
            && edgeConstraint wide == noConstraint
            && and (zipWith (go above) (edgeChildren wide) (edgeChildren narrow))

{- | Union automata without discarding open recursive references.

A closed operand and an ordinary node give their outgoing alternatives, and
the union concatenates them. A reference, and an open operand that is not an
ordinary node, has no alternatives until its binder closes. The union keeps
such operands in a union node until substitution supplies the referenced
automata. A binder drops a reference to itself at the root of its body, as
the least fixed point does. A union does not add a constructor to any
accepted term.
-}
{-# INLINEABLE union #-}
union :: (Hashable symbol, Typeable symbol) => [Node symbol] -> Node symbol
union nodes
    | all hasEdges nodes = Node (concatMap nodeEdges nodes)
    | otherwise = createUnion (Node (concatMap nodeEdges ready) : deferred)
  where
    (ready, deferred) = partition hasEdges nodes
    hasEdges (InternedNode _) = True
    hasEdges node = Set.null (freeVars node)

{- | Recognize a term with an explicit pure constraint interpreter.

The edges of a node are tried in order, and the children of an edge from left
to right. When the search comes to a subterm again with the same node, it uses
the first result. So each node is decided at most once at each position in the
term.
-}
{-# INLINEABLE acceptsWith #-}
acceptsWith ::
    (Hashable symbol, Typeable symbol) =>
    (Constraint -> Term symbol -> Bool) -> Node symbol -> Term symbol -> Bool
acceptsWith acceptsConstraint node = runIdentity . acceptsBy nodeEdges edgeSymbol edgeChildren check node
  where
    check _ edge term = Identity $ acceptsConstraint (edgeConstraint edge) term

-- | Tables for removal of redundant alternatives.
genericWithoutRedundantEdgesCache :: TypeableMemoCache
genericWithoutRedundantEdgesCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericWithoutRedundantEdgesCache #-}

{- | Remove alternatives implied by another alternative at each node.

Only a node without free recursive variables is changed, because the
comparison intersects alternatives. A recursive node compares the alternatives
of its unfolding, and keeps the alternatives of its body that remain. A node
that refers to an enclosing recursive node keeps all of its alternatives.
-}
{-# INLINEABLE withoutRedundantEdges #-}
withoutRedundantEdges ::
    forall symbol.
    (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol
withoutRedundantEdges node = memoTypeableWith @symbol genericWithoutRedundantEdgesCache go node
  where
    go = mapNodesStep withoutRedundantEdges dropReds
      where
        dropReds n@(Node es) | Set.null (freeVars n) = Node (dropRedundantEdges es)
        dropReds n@(InternedMu mu)
            | Set.null (freeVars n)
            , InternedNode body <- internedMuBody mu =
                let self = RecInt (internedMuId mu)
                    kept = Set.fromList (dropRedundantEdges (nodeEdges n))
                    -- The alternative of the unfolding that a body alternative becomes.
                    unfolded e = setChildren e (map (substFree self n) (edgeChildren e))
                    es = internedNodeEdges body
                    es' = filter ((`Set.member` kept) . unfolded) es
                 in if length es' == length es then n else Mu $ \r -> substFree self r (Node es')
        dropReds n = n

{- | Iterate until stable, or until the function has been applied the given
number of times. The result is the last value.
-}
fixWithin :: (Eq a) => Int -> (a -> a) -> a -> a
fixWithin rounds f x
    | rounds <= 0 || x' == x = x
    | otherwise = fixWithin (rounds - 1) f x'
  where
    x' = f x

-- | Iterate until stable with no iteration bound.
fixUnbounded :: (Eq a) => (a -> a) -> a -> a
fixUnbounded f x
    | x' == x = x
    | otherwise = fixUnbounded f x'
  where
    x' = f x

{- | Group values by a key.

Key equality defines each group. Different keys remain separate even when
their hashes are equal. Each group keeps its input order; the order of groups
is not specified.
-}
clusterByHash :: (Hashable k) => (a -> k) -> [a] -> [[a]]
clusterByHash key ls =
    map reverse $ HashMap.elems $ HashMap.fromListWith (++) [(key x, [x]) | x <- ls]

{- | Join two lists by equal keys and combine matching pairs.

As for 'clusterByHash', the table is keyed by the key itself, so the combining
function sees exactly the pairs whose keys are equal however the key hashes.
-}
hashJoin :: (Hashable k) => (a -> k) -> (a -> a -> b) -> [a] -> [a] -> [b]
hashJoin key j l1 l2 =
    [j x y | x <- l1, y <- HashMap.findWithDefault [] (key x) right]
  where
    right = HashMap.fromListWith (++) [(key x, [x]) | x <- l2]

-- Paths into graphs

instance (Hashable symbol, Typeable symbol) => Pathable (Node symbol) (Node symbol) where
    type Emptyable (Node symbol) = Node symbol

    getPath _ EmptyNode = EmptyNode
    getPath EmptyPath n = n
    getPath p n@(Mu _) = getPath p (unfoldOuterRec n)
    getPath p n@(InternedUnion _) = getPath p (Node $ nodeEdges n)
    getPath (ConsPath (ChildIndex p) ps) (Node es) = union (mapMaybe (\e -> getPath ps <$> edgeChildren e !? p) es)
    getPath p _ = error $ "getPath: unexpected path " <> show p <> " for unresolved node"

    getAllAtPath _ EmptyNode = []
    getAllAtPath EmptyPath n = [n]
    getAllAtPath p n@(Mu _) = getAllAtPath p (unfoldOuterRec n)
    getAllAtPath p n@(InternedUnion _) = getAllAtPath p (Node $ nodeEdges n)
    getAllAtPath (ConsPath (ChildIndex p) ps) (Node es) = concatMap (getAllAtPath ps) (mapMaybe (\e -> edgeChildren e !? p) es)
    getAllAtPath p _ = error $ "getAllAtPath: unexpected path " <> show p <> " for unresolved node"

    modifyAtPath f EmptyPath n = f n
    modifyAtPath _ _ EmptyNode = EmptyNode
    modifyAtPath f p n@(Mu _) = modifyAtPath f p (unfoldOuterRec n)
    modifyAtPath f p n@(InternedUnion _) = modifyAtPath f p (Node $ nodeEdges n)
    modifyAtPath f (ConsPath p ps) (Node es) = Node (map goEdge es)
      where
        goEdge e = setChildren e (adjustAt p (modifyAtPath f ps) (edgeChildren e))
    modifyAtPath _ p _ = error $ "modifyAtPath: unexpected path " <> show p <> " for unresolved node"

instance (Hashable symbol, Typeable symbol) => Pathable [Node symbol] (Node symbol) where
    type Emptyable (Node symbol) = Node symbol

    getPath EmptyPath ns = union ns
    getPath (ConsPath (ChildIndex p) ps) ns = maybe EmptyNode (getPath ps) (ns !? p)

    getAllAtPath EmptyPath _ = []
    getAllAtPath (ConsPath (ChildIndex p) ps) ns = maybe [] (getAllAtPath ps) (ns !? p)

    modifyAtPath _ EmptyPath ns = ns
    modifyAtPath f (ConsPath p ps) ns = adjustAt p (modifyAtPath f ps) ns

{- | Paths to every reachable node that satisfies a predicate.

Linear in the number of paths and exponential in the size of the graph, so
use it on very small graphs only. A recursive node contributes no paths: the
search does not unfold recursion, so a match below a 'Mu' is not reported.
-}
pathsMatching :: (Node symbol -> Bool) -> Node symbol -> [Path]
pathsMatching _ EmptyNode = []
pathsMatching _ (InternedMu _) = []
pathsMatching _ (InternedUnion _) = []
pathsMatching f n@(InternedNode node) = concatMap pathsMatchingEdge (internedNodeEdges node) ++ [EmptyPath | f n]
  where
    pathsMatchingEdge e = concat $ zipWith (\i x -> map (ConsPath i) $ pathsMatching f x) [0 ..] (edgeChildren e)
pathsMatching _ (Rec _) = error "pathsMatching: unexpected Rec"

-- | Restrict a graph to the terms that contain the given path.
requirePath ::
    (Hashable symbol, Typeable symbol) => Path -> Node symbol -> Node symbol
requirePath EmptyPath n = n
requirePath _ EmptyNode = EmptyNode
requirePath p n@(Mu _) = requirePath p (unfoldOuterRec n)
requirePath p n@(InternedUnion _) = requirePath p (Node $ nodeEdges n)
requirePath p@(ConsPath (ChildIndex index) _) (Node es) =
    Node
        [ setChildren e (requirePathList p (edgeChildren e))
        | index >= 0
        , e <- es
        , compareLength (edgeChildren e) index == GT
        ]
requirePath _ (Rec _) = error "requirePath: unexpected Rec"

-- | Variant of 'requirePath' for a child list.
requirePathList ::
    (Hashable symbol, Typeable symbol) =>
    Path -> [Node symbol] -> [Node symbol]
requirePathList EmptyPath ns = ns
requirePathList (ConsPath p ps) ns = adjustAt p (requirePath ps) ns
