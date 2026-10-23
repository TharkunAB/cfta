{-# LANGUAGE OverloadedStrings #-}

{- | Exclude fixed templates from a finite program graph before enumeration.
The caller supplies validated, uniformly decreasing rewrite templates.
The caller disables this path for a type constructor with the app/4 shape.
Program nodes must form a finite DAG.
The compiler keeps annotation subtrees unchanged.

After compilation, one reduction pass propagates the original equalities.
The reduction can narrow annotation nodes.
The helper forces the resulting program projection before enumeration.
The oracle retains entries without a proof that a compiled template covers them.
The remaining entries keep their original order and duplicates.

The compiler preserves the complete finite program language after exclusion.
This statement does not prove equality of recursive annotation cutoff streams.
Input and output graph caps do not bound transient constructor allocation.
-}
module Specftacular.CompiledPruning (preparePruning) where

import qualified Control.Monad.State.Strict as State
import Data.CFTA.Constraint (noConstraint)
import Data.CFTA.Equality (reducePartially)
import Data.CFTA.Interned (
    Edge,
    Node (..),
    NodeId,
    edgeChildren,
    edgeConstraint,
    edgeSymbol,
    nodeIdentity,
    setChildren,
 )
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Template (Template (..), exclude)
import Data.Either (fromRight)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

{- | Select a graph and the remaining templates for the existing oracle.
Unsupported input or a rejected result keeps the original graph and full list.
A local traversal table shares rebuilt program nodes. The remaining templates
depend on the templates only, so a partial application computes them once for
all its graphs.
-}
preparePruning :: [Template Symbol] -> Node Symbol -> (Node Symbol, [Template Symbol])
preparePruning templates = \root -> fromRight (root, templates) (prepared root)
  where
    selected = filter eligible templates
    residual = residualTemplates selected templates
    prepared root = do
        compiled <- compileTemplates selected root
        (before, beforeOpaque) <- graph True (4096, 65536) compiled
        ( Map.size before
                + sum [length es | (_, es) <- Map.elems before]
                + Set.size beforeOpaque
            )
            `seq` pure ()
        let reduced = reducePartially compiled
        (after, afterOpaque) <- graph False (4096, 65536) reduced
        ( Map.size after
                + sum [length es | (_, es) <- Map.elems after]
                + Set.size afterOpaque
                + Set.size (afterOpaque `Set.difference` beforeOpaque)
            )
            `seq` pure (reduced, residual)

-- | Admit only application patterns whose annotation positions are holes.
eligible :: Template Symbol -> Bool
eligible template@(TemplateNode "app" [_, _, _, _]) = program template
  where
    program Hole = True
    program (TemplateNode "app" [Hole, marker, f, x]) =
        marker `elem` [Hole, TemplateNode "(->)" []] && program f && program x
    program (TemplateNode _ [Hole]) = True
    program _ = False
eligible _ = False

{- | Count the least program leaves that can match an eligible template.
Annotations and the arrow marker do not contribute. Unknown forms return zero,
so the bound cannot remove a template that this function does not recognize.
-}
minimumLeaves :: Template Symbol -> Integer
minimumLeaves Hole = 1
minimumLeaves (TemplateNode "app" [_, _, f, x]) = minimumLeaves f + minimumLeaves x
minimumLeaves (TemplateNode _ [_]) = 1
minimumLeaves _ = 0

-- | Classify raw program child positions. Annotation and marker nodes stay opaque.
positions :: Edge Symbol -> Either String [Int]
positions edge = case (edgeSymbol edge, edgeChildren edge) of
    ("app", [_, marker, _, _])
        | singletonArrow marker -> Right [2, 3]
        | otherwise -> Left "UNKNOWN marker is not the fixed singleton arrow"
    ("filter", [_, _]) -> Right [1]
    (_, [_]) -> Right []
    _ -> Left "UNKNOWN unrecognized program constructor or arity"
  where
    singletonArrow (Node [marker]) =
        edgeSymbol marker == "(->)"
            && null (edgeChildren marker)
            && edgeConstraint marker == noConstraint
    singletonArrow _ = False

{- | Check the finite program projection and direct opaque child roots.
The compiler requires disjoint roles. One reduction pass can merge roles.
The check does not traverse the opaque annotation closure.
These graph caps do not bound allocation during construction.
-}
graph ::
    Bool -> (Int, Int) -> Node Symbol -> Either String (Map.Map NodeId (Node Symbol, [Edge Symbol]), Set.Set NodeId)
graph strictRoles (maxNodes, maxEdges) root = visit Set.empty root (Map.empty, Set.empty)
  where
    visit _ EmptyNode accumulated = Right accumulated
    visit _ (Rec _) _ = Left "UNKNOWN free recursive program reference"
    visit _ (InternedMu _) _ = Left "UNKNOWN recursive program node"
    visit _ (InternedUnion _) _ = Left "UNKNOWN union program node"
    visit ancestors node (seen, opaque)
        | Set.member ident ancestors = Left "UNKNOWN projected program cycle"
        | Map.member ident seen = Right (seen, opaque)
        | Map.size seen >= maxNodes = Left "UNKNOWN projected graph cap"
        | otherwise = case node of
            Node edges -> do
                roles <- traverse positions edges
                let edgesSoFar = length edges + sum [length es | (_, es) <- Map.elems seen]
                if edgesSoFar > maxEdges
                    then Left "UNKNOWN projected edge cap"
                    else do
                        let seen' = Map.insert ident (node, edges) seen
                        (finished, opaque') <- foldChildren (Set.insert ident ancestors) (seen', opaque) (zip edges roles)
                        if strictRoles && any (`Map.member` finished) (Set.toList opaque')
                            then Left "UNKNOWN node has both program and opaque roles"
                            else Right (finished, opaque')
            _ -> Left "UNKNOWN recursive or union program node"
      where
        ident = nodeIdentity node
    foldChildren _ accumulated [] = Right accumulated
    foldChildren ancestors (seen, opaque) ((edge, selected) : rest) = do
        let children = zip [0 ..] (edgeChildren edge)
            opaque' = Set.union opaque (Set.fromList [nodeIdentity n | (i, n) <- children, i `notElem` selected])
        next <- foldNodes ancestors (seen, opaque') [n | (i, n) <- children, i `elem` selected]
        foldChildren ancestors next rest
    foldNodes _ accumulated [] = Right accumulated
    foldNodes ancestors accumulated (child : rest) = do
        next <- visit ancestors child accumulated
        foldNodes ancestors next rest

{- | Keep the original constraints and child positions. Reuse original opaque nodes.
A local table shares this finite traversal only. It is not a global cache.
-}
compileTemplates :: [Template Symbol] -> Node Symbol -> Either String (Node Symbol)
compileTemplates templates root
    | null templates = Left "SKIP no eligible templates"
    | not (all eligible templates) = Left "SKIP template needs annotation matching"
    | otherwise = do
        (source, originalOpaque) <- graph True (256, 4096) root
        let result = fst (State.evalState (build source root) Map.empty)
        (finished, finalOpaque) <- graph True (4096, 65536) result
        if not (finalOpaque `Set.isSubsetOf` originalOpaque)
            then Left "UNKNOWN an opaque node changed"
            else
                if Map.size finished > 4096
                    then Left "UNKNOWN output graph cap"
                    else Right result
  where
    -- A fixed ordered subset shares one template catalog across all nodes.
    sizedTemplates = [(minimumLeaves template, template) | template <- templates]
    exclusions =
        Map.fromList
            [ (bound, exclude [template | (needed, template) <- sizedTemplates, needed <= bound])
            | bound <- Set.toAscList (Set.fromList (map fst sizedTemplates))
            ]
    excludeHere bound node = maybe node (\(_, prune) -> prune node) (Map.lookupLE bound exclusions)
    -- Bounds describe the original graph without equality restrictions.
    -- Exclusion can only reduce its language. Integer prevents DAG-size overflow.
    -- Skipping an impossible template can retain more runs of the same term
    -- in an ambiguous graph. The complete finite term language is unchanged.
    build ::
        Map.Map NodeId (Node Symbol, [Edge Symbol]) ->
        Node Symbol ->
        State.State (Map.Map NodeId (Node Symbol, Integer)) (Node Symbol, Integer)
    build _ EmptyNode = pure (EmptyNode, 0)
    build source node = do
        known <- State.gets (Map.lookup (nodeIdentity node))
        case known of
            Just result -> pure result
            Nothing -> do
                let (_, edges) = source Map.! nodeIdentity node
                changed <- traverse (edge source) edges
                let bound = maximum (0 : map snd changed)
                    result = (excludeHere bound (Node (map fst changed)), bound)
                State.modify' (Map.insert (nodeIdentity node) result)
                pure result
    edge ::
        Map.Map NodeId (Node Symbol, [Edge Symbol]) ->
        Edge Symbol ->
        State.State (Map.Map NodeId (Node Symbol, Integer)) (Edge Symbol, Integer)
    edge source original = do
        let selected = either error id (positions original)
        children <-
            sequence
                [ if index `elem` selected then build source child else pure (child, 0)
                | (index, child) <- zip [0 ..] (edgeChildren original)
                ]
        let bound = if null selected then 1 else sum (map snd children)
        pure (setChildren original (map fst children), bound)

{- | Prove inclusion from exact template roots and wildcard children only.
A failed check is not proof that the two template languages are disjoint.
-}
covers :: Template Symbol -> Template Symbol -> Bool
covers Hole _ = True
covers (TemplateNode symbol parts) (TemplateNode target children) =
    symbol == target
        && length parts == length children
        && and (zipWith covers parts children)
covers _ _ = False

{- | Keep the original order and duplicates of all templates without a proof.
The first list is the fixed set that was compiled at this bucket entry.
-}
residualTemplates :: [Template Symbol] -> [Template Symbol] -> [Template Symbol]
residualTemplates compiled = filter (\template -> not (any (`covers` template) compiled))
