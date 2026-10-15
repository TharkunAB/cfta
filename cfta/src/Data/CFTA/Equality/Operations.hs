{-# LANGUAGE OverloadedStrings #-}

{- | Operations that interpret path equalities: reduction, concrete
membership, and template restriction. Most users import "Data.CFTA.Equality".

'reducePartially' and 'reduceEdgeIntersection' narrow children by the
'equalities' of the edge constraints. They are memoized per alphabet.
-}
module Data.CFTA.Equality.Operations (
    accepts,
    reducePartially,
    reduceEdgeIntersection,
    reduceEqConstraints,
    termsMatching,
) where

import Data.Hashable (Hashable (..))
import qualified Data.IntMap.Strict as IntMap
import Data.List (compareLength, partition, (!?))
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (Typeable)

import Data.CFTA.Enumeration (provablyEmpty, reachesConstrainedMu, unconstrained)
import Data.CFTA.Equality.Constraint
import Data.CFTA.Internal.Tree (adjustAt)
import Data.CFTA.Interned
import Data.CFTA.Interned.Memo (
    TypeableMemoCache,
    memo2TypeableWith,
    newTypeableMemoCache,
 )
import Data.CFTA.Interned.Operations (mergeAlternatives)
import Data.CFTA.Path (ChildIndex (..), Path (..), Pathable (..))
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Template (Template (..), restrict)
import Data.CFTA.Term (Term)

------------
------ Membership
------------

{- | Recognize through the common traversal and the equality interpreter. A
constraint's residual beyond its path equalities is not decided here.
-}
accepts :: (Hashable symbol, Typeable symbol) => Node symbol -> Term symbol -> Bool
accepts = acceptsWith equalitiesHold

------------------------------------
------ Reduction
------------------------------------

{- | Propagate equality constraints through one reduction pass.

One pass narrows every child by the constraints that reach it, but a nested
constrained edge can narrow a child after an outer edge has already read it.
Iterate to a fixpoint, as 'fixUnbounded' does, when every
constrained position must agree with every other.

The pass does not unfold a recursive node that has constraints. A class that
reaches into such a node, or ends above one, stays unreduced (see
'reduceEqConstraints'). The language does not change, because enumeration and
'accepts' still check that class. When the class ends above such a node and
the nodes at its paths provably share no term, the edge becomes empty instead.
-}
reducePartially ::
    (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol
reducePartially = reducePartially' EmptyConstraints

genericReducePartiallyCache :: TypeableMemoCache
genericReducePartiallyCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericReducePartiallyCache #-}

reducePartially' ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    EqConstraints -> Node symbol -> Node symbol
reducePartially' constraints node =
    memo2TypeableWith @symbol genericReducePartiallyCache go constraints node
  where
    go :: EqConstraints -> Node symbol -> Node symbol
    go _ EmptyNode = EmptyNode
    go _ (Mu n) = Mu n
    go _ n@(InternedUnion _) = n
    go inheritedEcs n@(Node _) = modifyNode n $ \es ->
        map
            (reduceChildren inheritedEcs . reduceEdgeIntersection inheritedEcs)
            es
    go _ (Rec _) = error "reducePartially: unexpected Rec"

    reduceChildren :: EqConstraints -> Edge symbol -> Edge symbol
    reduceChildren inheritedEcs e =
        setChildren e $
            reduceWithInheritedEcs (inheritedEcs `combineEqConstraints` equalities (edgeConstraint e)) (edgeChildren e)

    -- Reduce children with inherited constraints.
    --
    -- This function is used to avoid infinite unfolding of recursive nodes,
    -- and we do this by passing constraints from the current edge and ancestors to descendants.
    -- For example, let `tau` be "any" node, and we define
    --
    -- > let n1 = Node [ mkEdge "Pair" [tau, tau] (equalityConstraint $ mkEqConstraints [[path [0, 0], path [0, 1], path [1]]])]
    -- > let n2 = Node [ Edge "Pair" [tau, tau] ]
    -- > let n  = Node [ mkEdge "Pair" [n1, n2]   (equalityConstraint $ mkEqConstraints [[path [0, 0], path [0, 1], path [1]]])]
    --
    -- If `reducePartially n` does not propagate constraints down to its children `n1` or `n2`,
    -- the reduction can expand `tau` without end between rounds.
    --
    -- To break such cycles, we actively pass constraints down to children.
    -- In this example, we first call `reducePartially' EmptyConstraints n` at the top level, where the inherited constraint is empty,
    -- so we only need to consider the constraints from the current edge.
    -- Then, we pass the constraints `0.0=0.1=1` down to its children, and `n1` receives `0=1` and `n2` receives nothing.
    -- Next, we reduce the children of `n` by calling `reducePartially' (mkEqConstraints [[path [0], path [1]]]) n1`.
    -- At this node, we will have to combine the inherited constraints `0=1` and the local constraints `0.0=0.1=1`.
    -- Now, we can see that these two constraints contain a contradiction that requires `0=0.0=0.1`, so we can drop the edge.
    --
    -- The inherited constraints do not stop every recursive cycle. The pass
    -- must also not unfold a recursive node that has constraints. 'go'
    -- returns a recursive node unchanged. 'reduceEqConstraints' does not
    -- reduce a class whose paths meet such a node, or end above one. Without
    -- the last rule, an intersection at the end of a path can unfold the
    -- node, and a narrowed child can then contain its own ancestor. The memo
    -- then demands its own unfinished result. The test "stops when a narrowed
    -- child contains its ancestor" has such an input. The standalone
    -- reproduction is lean/repro/OuterCallerCycle.hs.
    --
    -- One pass ends in two cases. If no reduced path meets a recursive node,
    -- at its end or before it, the pass unfolds nothing. An intersection is
    -- then not higher than the node that it replaces, so each narrowed child
    -- is lower than its parent. If no node at the end of a reduced path has a
    -- constraint, the narrowing adds no constraint. Then the pass changes no
    -- node below the deepest constrained edge of the input, and below that
    -- depth it stops at each recursive node. No proof covers the other
    -- inputs. A class over paths of unequal length can move a constrained
    -- node into the unfolding of a recursive node without constraints,
    -- deeper than it was. No proof shows that a repetition of passes ends
    -- either. The reduction tests "stops on the example that needs inherited
    -- constraints", "stops on a class over three recursive children", and
    -- "stops on classes over recursive children" check finite examples and
    -- random recursive inputs.
    reduceWithInheritedEcs :: EqConstraints -> [Node symbol] -> [Node symbol]
    reduceWithInheritedEcs EqContradiction children = map (const EmptyNode) children
    reduceWithInheritedEcs inheritedEcs children = zipWith (\i -> reducePartially' (eqConstraintsDescend inheritedEcs i)) [0 ..] children
{-# INLINEABLE reducePartially' #-}
{-# SPECIALIZE reducePartially' :: EqConstraints -> Node Symbol -> Node Symbol #-}

genericReduceEdgeIntersectionCache :: TypeableMemoCache
genericReduceEdgeIntersectionCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericReduceEdgeIntersectionCache #-}

{- | Narrow an edge's children by its own equality constraints. The edge becomes
empty when its constraints contradict the inherited constraints.
-}
reduceEdgeIntersection ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    EqConstraints -> Edge symbol -> Edge symbol
reduceEdgeIntersection constraints edge =
    memo2TypeableWith @symbol genericReduceEdgeIntersectionCache go constraints edge
  where
    go :: EqConstraints -> Edge symbol -> Edge symbol
    go ecs e =
        mkEdge
            (edgeSymbol e)
            (reduceEqConstraints (equalities (edgeConstraint e)) ecs (edgeChildren e))
            (edgeConstraint e)
{-# INLINEABLE reduceEdgeIntersection #-}
{-# SPECIALIZE reduceEdgeIntersection :: EqConstraints -> Edge Symbol -> Edge Symbol #-}

{- | Apply the local equality classes to a child list. Make every child empty
when the local and inherited classes contradict each other.

One pass over the classes is not always enough: the intersection for one class
can narrow a node that a class earlier in the pass already read. Iterate the
reduction, as 'fixUnbounded' does, to get a fixpoint. The reduction does not
iterate by itself. The next pass reads the new nodes of this pass, so its
intersections miss the memo. A fixpoint at each edge made the term search of
the ECTA paper about 100 times slower than a fixpoint of 'reducePartially'.

A class stays unreduced when one of its paths meets a recursive node with
constraints, at the end of the path or before it. Unfolding such a node shows
its constrained edges again, and their reduction unfolds the node again. A
recursive node without constraints can unfold, because its unfolding has no
constraints to reduce. A class also stays unreduced when a node at the end of
one of its paths reaches a recursive node with constraints. The intersection
at that path would unfold the recursive node too. When only the end of a path
refuses a class (the nodes at its paths are closed, and one is or reaches a
recursive node with constraints), and the intersection of the nodes at its
paths provably accepts no term ('provablyEmpty'), every child becomes empty,
as for a contradiction.
-}
reduceEqConstraints ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    EqConstraints ->
    EqConstraints ->
    [Node symbol] ->
    [Node symbol]
reduceEqConstraints = go
  where
    propagateEmptyNodes :: [Node symbol] -> [Node symbol]
    propagateEmptyNodes ns = if EmptyNode `elem` ns then map (const EmptyNode) ns else ns

    go :: EqConstraints -> EqConstraints -> [Node symbol] -> [Node symbol]
    go EmptyConstraints EmptyConstraints origNs = origNs
    go ecs inheritedEcs origNs
        | constraintsAreContradictory (ecs `combineEqConstraints` inheritedEcs) = map (const EmptyNode) origNs
        | any emptyBelowEnd refused = map (const EmptyNode) origNs
        | otherwise = propagateEmptyNodes $ foldr reduceEClass withNeededChildren eclasses
      where
        (refused, eclasses) = partition (any (meetsConstrainedMu True origNs) . unPathEClass) (unsafeSubsumptionOrderedEclasses ecs)

        -- Only the end of a path refuses this class: the nodes at its paths
        -- are closed, and one is or reaches a recursive node with
        -- constraints. The check reads their intersection and puts it into
        -- no child.
        emptyBelowEnd :: PathEClass -> Bool
        emptyBelowEnd pec =
            not (any (meetsConstrainedMu False origNs) paths)
                && provablyEmpty (intersectList [getPath p origNs | p <- paths])
          where
            paths = Set.toList (unPathEClass pec)

        withNeededChildren = requireAll (Set.unions $ map unPathEClass eclasses) origNs

        intersectList :: [Node symbol] -> Node symbol
        intersectList [] = EmptyNode
        intersectList (n : ns) = foldr intersect n ns

        -- Narrow the node at each path of the class to the nodes at the other
        -- paths. The narrowing set is merged ('mergeAlternatives'): it can keep
        -- more terms, never fewer. At a merged ordinary root, intersection
        -- pairs each edge of the other side with at most one merged edge.
        reduceEClass :: PathEClass -> [Node symbol] -> [Node symbol]
        reduceEClass pec ns =
            editAll
                [ (p, intersect $ intersectList [mergeAlternatives (getPath other ns) | other <- Set.toAscList paths, other /= p])
                | p <- Set.toAscList paths
                ]
                ns
          where
            paths = unPathEClass pec

    -- Whether a path meets a recursive node with constraints, at the end of
    -- the path or before it. A free recursive reference counts as such a
    -- node: pruning a recursive body leaves references to the node that is
    -- being pruned, and its edges are not known there. So does a node with
    -- free references at the end of the path, and an unconstrained recursive
    -- node with free references is followed through its unfolding. A closed
    -- node at the end of the path that is, or reaches, a recursive node with
    -- constraints ('reachesConstrainedMu') counts only if the first argument
    -- is true.
    meetsConstrainedMu :: Bool -> [Node symbol] -> Path -> Bool
    meetsConstrainedMu belowEnd ns (ConsPath (ChildIndex index) rest) = maybe False (nodeMeetsConstrainedMu belowEnd rest) (ns !? index)
    meetsConstrainedMu _ _ EmptyPath = False

    nodeMeetsConstrainedMu :: Bool -> Path -> Node symbol -> Bool
    nodeMeetsConstrainedMu _ _ (Rec _) = True
    nodeMeetsConstrainedMu _ _ (InternedUnion _) = True
    nodeMeetsConstrainedMu _ _ n | numNestedMu n == 0 && null (freeVars n) = False
    nodeMeetsConstrainedMu belowEnd p n@(InternedMu _)
        | not (unconstrained n) = case p of
            EmptyPath | null (freeVars n) -> belowEnd
            _ -> True
        | null (freeVars n) = False
        | otherwise = nodeMeetsConstrainedMu belowEnd p (unfoldOuterRec n)
    nodeMeetsConstrainedMu belowEnd EmptyPath n = not (null (freeVars n)) || (belowEnd && reachesConstrainedMu n)
    nodeMeetsConstrainedMu belowEnd p (Node es) = any (\e -> meetsConstrainedMu belowEnd (edgeChildren e) p) es
    nodeMeetsConstrainedMu _ _ _ = False

-- | A trie of child positions that must exist. An empty map ends a required path.
newtype Needed = Needed (IntMap.IntMap Needed)

{- | Restrict a child list to the terms that contain every path, in one
traversal. This gives the same nodes as requiring the paths one at a time.
-}
requireAll ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    Set Path -> [Node symbol] -> [Node symbol]
requireAll paths = requireList (foldr insertNeeded (Needed IntMap.empty) paths)
  where
    insertNeeded EmptyPath needed = needed
    insertNeeded (ConsPath (ChildIndex index) rest) (Needed children) =
        Needed $ IntMap.alter (Just . insertNeeded rest . fromMaybe (Needed IntMap.empty)) index children

    requireList :: Needed -> [Node symbol] -> [Node symbol]
    requireList (Needed children) ns = IntMap.foldrWithKey (\index needed -> adjustAt (ChildIndex index) (requireNode needed)) ns children

    requireNode :: Needed -> Node symbol -> Node symbol
    requireNode (Needed children) n | IntMap.null children = n
    requireNode _ EmptyNode = EmptyNode
    requireNode needed n@(Mu _) = requireNode needed (Node $ nodeEdges n)
    requireNode needed n@(InternedUnion _) = requireNode needed (Node $ nodeEdges n)
    requireNode needed@(Needed children) (Node es) =
        Node
            [ setChildren e (requireList needed (edgeChildren e))
            | e <- es
            , compareLength (edgeChildren e) (fst (IntMap.findMax children)) == GT
            ]
    requireNode _ (Rec _) = error "requireAll: unexpected Rec"

-- | Edits at child positions: one at the end of a path, or the edits below an index.
data Edits symbol
    = EditAt (Node symbol -> Node symbol)
    | EditBelow (IntMap.IntMap (Edits symbol))

{- | Apply edits at several paths, none a prefix of another, in one traversal.
This gives the same nodes as 'modifyAtPath' at each path in turn.
-}
editAll ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    [(Path, Node symbol -> Node symbol)] -> [Node symbol] -> [Node symbol]
editAll edits = editList (foldr (uncurry insertEdit) (EditBelow IntMap.empty) edits)
  where
    insertEdit EmptyPath f _ = EditAt f
    insertEdit (ConsPath (ChildIndex index) rest) f (EditBelow children) =
        EditBelow $ IntMap.alter (Just . insertEdit rest f . fromMaybe (EditBelow IntMap.empty)) index children
    insertEdit (ConsPath _ _) _ leaf@(EditAt _) = leaf

    editList :: Edits symbol -> [Node symbol] -> [Node symbol]
    editList (EditAt _) ns = ns
    editList (EditBelow children) ns = IntMap.foldrWithKey (\index below -> adjustAt (ChildIndex index) (editNode below)) ns children

    editNode :: Edits symbol -> Node symbol -> Node symbol
    editNode (EditAt f) n = f n
    editNode _ EmptyNode = EmptyNode
    editNode below n@(Mu _) = editNode below (Node $ nodeEdges n)
    editNode below n@(InternedUnion _) = editNode below (Node $ nodeEdges n)
    editNode below (Node es) = Node (map (\e -> setChildren e (editList below (edgeChildren e))) es)
    editNode _ (Rec _) = error "editAll: unexpected Rec"

{- | Keep exactly the terms in a node that match a template.

The graph is restricted and then reduced, so a 'Hole' at a constrained
position can be narrowed by a concrete pattern at an equal one. 'restrict'
keeps an edge only if its symbol and arity can match, restricts its children
with the child templates, and keeps the edge constraints. The reduction only
narrows the children and removes no accepted term. So the result accepts
exactly the terms of the node that match the template. Recursive nodes expose
their constructor rows before restriction. A retained recursive cycle with no
constructor rows restricts to 'EmptyNode'.
-}
termsMatching ::
    (Hashable symbol, Typeable symbol) =>
    Template symbol -> Node symbol -> Node symbol
termsMatching Hole = id
termsMatching (AnyPrefix []) = id
termsMatching template = reducePartially . restrict template
