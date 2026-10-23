{-# LANGUAGE OverloadedStrings #-}

{- | Reject redundant partial terms during constrained enumeration.
Each suspended check belongs to one branch and resumes when its hole expands.
-}
module Specftacular.Pruning (prunedTerms, prunedPrograms) where

import Control.Monad (zipWithM)
import Data.CFTA.Equality (
    EnumerateM,
    Node (Mu, Node),
    PartialSymbol (..),
    TermFragment (..),
    UVar,
    edgeChildren,
    edgeSymbol,
    expandPartialTermFrag,
    getUVarRepresentative,
    getUnexpandedNode,
    intToUVar,
    nodeEdges,
    runsInterned,
    termsPruneUntil,
    termsPruneWith,
    uvarToInt,
 )
import Data.CFTA.Interned.Memo (memo2)
import Data.CFTA.Symbol (Symbol (Symbol))
import Data.CFTA.Template (Template (..))
import qualified Data.CFTA.Term as CT
import Data.Hashable (Hashable)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (find)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, mapMaybe)
import qualified Data.Set as Set
import qualified Data.Text as Text

-- | The remaining parts of one match, each waiting for an enumeration hole.
type Pending = [(Template Symbol, UVar)]

-- | A partial term with explicit markers for unresolved holes and recursion.
type PartialTerm = CT.Term (PartialSymbol Symbol)

{- | Enumerate terms while rejecting branches that contain a template.
The templates must describe redundant program applications. Type annotations
are checked only where a template requires them.
Every program application must use the fixed singleton arrow marker. The
caller must disable pruning if a type constructor also has the app/4 shape.
The early check omits the marker only under these encoding assumptions.
-}
prunedTerms :: [Template Symbol] -> Node Symbol -> [CT.Term Symbol]
prunedTerms [] = map fst . runsInterned "Mu"
prunedTerms templates = termsPruneWith "Mu" [] order oracle
  where
    (order, oracle) = templateOracle templates

{- | The programs of 'prunedTerms', with their types left open. A program has
the placeholder symbol @?@ at each type position that the enumeration did not
expand: the annotation and the arrow marker of an application, the type of a
filter and of a symbol, and each position below them. The enumeration expands
a hole at a type position only when a template check waits for it, and a
branch stops when only such holes remain and no check waits for them (see
'termsPruneUntil'). So a program appears once for each way to reach it, and
not once for each of its typings.

A typing replaces the expansion of the types. It starts at the type of the
root hole (the first argument), and each expansion of a hole at a program
position extends it with the new fragment (the second argument, with the
number of the hole and the fragment, where the hole @?program#n@ stands for
the UVar @n@). A fragment without a typing ends the branch. Before the choice
at a hole at a program position, the hole keeps only the edges whose
annotation can hold its type (the fifth argument) and the constants that can
have its type (the fourth argument). The key of a hole (the third argument)
stands for its type: two holes with the same key and the same node keep the
same edges. After each typing, each open hole at a program position must
keep an edge, else the branch ends. A typing only becomes more specific, and
both checks must hold for a more specific type only if they hold for the
type, so the hole would have no edge when it expands. The caller must type
each program again, as 'generalizeCarriers' does, and must not read the
annotations.
-}
prunedPrograms ::
    (Hashable k) =>
    t ->
    (Int -> CT.Term Symbol -> t -> Maybe t) ->
    (t -> Int -> k) ->
    (k -> Symbol -> Bool) ->
    (k -> Node Symbol -> Bool) ->
    [Template Symbol] ->
    Node Symbol ->
    [CT.Term Symbol]
prunedPrograms start extend holeKey fits admits templates =
    map (openTypes False)
        . termsPruneUntil ([], IntSet.empty, IntSet.singleton 0, start) typesLast narrow atTypes typedTypes
  where
    -- The state: the pending template checks, the holes at type positions,
    -- the open holes at program positions, and the typing.
    (order, oracle) = templateOracle templates
    typesLast (pending, types, _, _) candidates =
        case order pending candidates of
            Just uv -> Just uv
            Nothing -> find (\uv -> uvarToInt uv `IntSet.notMember` types) candidates
    atTypes (pending, types, _, _) uv = uvarToInt uv `IntSet.member` types && all (all ((/= uv) . snd)) pending
    recordTypes (pending, types, open, typing) uv input = do
        let types' = case input of
                Left fragment -> typePositions (uvarToInt uv `IntSet.member` types) fragment types
                Right _ -> types
        (prune, pending') <- if null templates then pure (False, pending) else oracle pending uv input
        pure (prune, (pending', types', open, typing))
    typedTypes state@(_, types, _, _) uv input = do
        (prune, state'@(pending, types', open, typing)) <- recordTypes state uv input
        case input of
            Left fragment
                | not prune
                , uvarToInt uv `IntSet.notMember` types -> do
                    partial <- expandPartialTermFrag fragment
                    case extend (uvarToInt uv) (openProgram False partial) typing of
                        Nothing -> pure (True, state')
                        Just typing' -> do
                            let open' = foldr IntSet.insert (IntSet.delete (uvarToInt uv) open) (programHoles False fragment)
                            dead <- or <$> mapM (\h -> maybe False (emptyAt typing' h) <$> getUnexpandedNode (intToUVar h)) (IntSet.toList open')
                            pure (if dead then (True, state') else (False, (pending, types', open', typing')))
            _ -> pure (prune, state')
    narrow (_, types, _, typing) uv n = case n of
        Mu _ -> n
        _
            | uvarToInt uv `IntSet.member` types -> n
            | otherwise -> narrowAt n (holeKey typing (uvarToInt uv))
    emptyAt typing h n = case n of
        Mu _ -> False
        _ -> null (nodeEdges (narrowAt n (holeKey typing h)))
    -- One table for each call.
    narrowAt = memo2 (\n k -> Node [e | e <- nodeEdges n, keeps k e])
    keeps k e = case (edgeSymbol e, edgeChildren e) of
        ("app", [annotation, _, _, _]) -> admits k annotation
        ("filter", [annotation, _]) -> admits k annotation
        (symbol, [annotation]) -> admits k annotation && fits k symbol
        _ -> True

{- | The holes of a fragment at program positions: the function and
the argument of an application, and the program of a filter. With 'True',
the fragment is at a type position.
-}
programHoles :: Bool -> TermFragment Symbol -> [Int]
programHoles isType fragment = case fragment of
    TermFragmentUVar uv
        | isType -> []
        | otherwise -> [uvarToInt uv]
    TermFragmentNode symbol children
        | isType -> []
        | otherwise -> case (symbol, children) of
            ("app", [_, _, function, argument]) -> programHoles False function ++ programHoles False argument
            ("filter", [_, term]) -> programHoles False term
            _ -> []

{- | Add the holes of a fragment at type positions: the annotation and the
arrow marker of an application, the type of a filter and of a symbol, and
each hole below a type position. With 'True', the fragment is at a type
position.
-}
typePositions :: Bool -> TermFragment Symbol -> IntSet -> IntSet
typePositions isType fragment types = case fragment of
    TermFragmentUVar uv
        | isType -> IntSet.insert (uvarToInt uv) types
        | otherwise -> types
    TermFragmentNode symbol children
        | isType -> foldr (typePositions True) types children
        | otherwise -> case (symbol, children) of
            ("app", [annotation, marker, function, argument]) ->
                foldr (typePositions True) (foldr (typePositions False) types [function, argument]) [annotation, marker]
            ("filter", [annotation, term]) -> typePositions True annotation (typePositions False term types)
            _ -> foldr (typePositions True) types children

{- | A term of 'termsPruneUntil' with @?@ at its holes at type positions, as
'typePositions' finds them. With 'True', the term is at a type position. A
hole at a program position is an error, because the stop rule of
'prunedPrograms' accepts only holes at type positions.
-}
openTypes :: Bool -> PartialTerm -> CT.Term Symbol
openTypes isType (CT.Node symbol children) = case symbol of
    UVarHole _
        | isType -> CT.Node "?" []
        | otherwise -> error "prunedPrograms: a hole at a program position"
    TruncatedRecursion -> CT.Node "Mu" []
    ConcreteSymbol concrete
        | isType -> CT.Node concrete (map (openTypes True) children)
        | otherwise -> case (concrete, children) of
            ("app", [annotation, marker, function, argument]) ->
                CT.Node concrete [openTypes True annotation, openTypes True marker, openTypes False function, openTypes False argument]
            ("filter", [annotation, term]) -> CT.Node concrete [openTypes True annotation, openTypes False term]
            _ -> CT.Node concrete (map (openTypes True) children)

{- | 'openTypes' for a partial program, with @?program@ at each hole at
a program position.
-}
openProgram :: Bool -> PartialTerm -> CT.Term Symbol
openProgram isType (CT.Node symbol children) = case symbol of
    UVarHole uv
        | isType -> CT.Node "?" []
        | otherwise -> CT.Node (Symbol ("?program#" <> Text.pack (show (uvarToInt uv)))) []
    TruncatedRecursion -> CT.Node "Mu" []
    ConcreteSymbol concrete
        | isType -> CT.Node concrete (map (openProgram True) children)
        | otherwise -> case (concrete, children) of
            ("app", [annotation, marker, function, argument]) ->
                CT.Node
                    concrete
                    [openProgram True annotation, openProgram True marker, openProgram False function, openProgram False argument]
            ("filter", [annotation, term]) -> CT.Node concrete [openProgram True annotation, openProgram False term]
            _ -> CT.Node concrete (map (openProgram True) children)

{- | The expansion order and the oracle of 'prunedTerms'. The order takes
the holes that a suspended check waits for first. The oracle rejects a
branch when a template matches one of its programs.
-}
templateOracle ::
    [Template Symbol] ->
    ( [Pending] -> [UVar] -> Maybe UVar
    , [Pending] -> UVar -> Either (TermFragment Symbol) (Node Symbol) -> EnumerateM Symbol (Bool, [Pending])
    )
templateOracle templates = (order, oracle)
  where
    earlyTemplates = mapMaybe structuralTemplate templates
    earlyCandidatesFor = indexTemplates earlyTemplates
    rejectEarly fragment@(TermFragmentNode symbol children)
        | (symbol, length children) `elem` [("app", 4), ("filter", 2)] =
            any redundant (programs (fragmentTerm fragment))
      where
        redundant term = any (\template -> matchPartial template term == Just []) (earlyCandidatesFor term)
    rejectEarly _ = False
    candidatesFor = indexTemplates templates
    order pending candidates =
        let waiting = Set.fromList (map snd (concat pending))
         in find (`Set.member` waiting) candidates
    oracle :: [Pending] -> UVar -> Either (TermFragment Symbol) (Node Symbol) -> EnumerateM Symbol (Bool, [Pending])
    oracle pending _ (Right _) = pure (False, pending)
    oracle pending _ (Left fragment)
        | rejectEarly fragment = pure (True, pending)
    -- This concrete root starts no program match, and no check waits.
    oracle [] _ (Left (TermFragmentNode symbol children))
        | (symbol, length children) `notElem` [("app", 4), ("filter", 2)] = pure (False, [])
    oracle pending uv (Left fragment) = do
        partial <- expandPartialTermFrag fragment
        resumed <- traverse (resume uv partial) pending
        let started = [matchPartial template term | term <- programs partial, template <- candidatesFor term]
            checks = catMaybes (resumed ++ started)
        pure (any null checks, filter (not . null) checks)

-- | A fixed program head and the number of applications in its function spine.
type SpineKey = (Symbol, Int)

{- | Cache compatible templates for each fixed head. Keep their input order.
Only exact application and constant nodes fix a template head. Prefixes,
wildcards, and unrecognized spine nodes remain generic. Unknown program heads
use all templates. This index does not prove a match or inspect annotations.
-}
indexTemplates :: [Template Symbol] -> PartialTerm -> [Template Symbol]
indexTemplates templates = select
  where
    tagged = zip [0 :: Int ..] templates
    generic = IntMap.fromList [(i, t) | (i, t) <- tagged, Nothing <- [templateSpine t]]
    fallback = IntMap.elems generic
    fixed = Map.fromListWith IntMap.union [(key, IntMap.singleton i t) | (i, t) <- tagged, Just key <- [templateSpine t]]
    buckets = Map.map (IntMap.elems . IntMap.union generic) fixed
    select term = case partialSpine term of
        Nothing -> templates
        Just key -> Map.findWithDefault fallback key buckets

-- | Read an exact raw template spine. Other template forms cannot fix a key.
templateSpine :: Template Symbol -> Maybe SpineKey
templateSpine = go 0
  where
    go count (TemplateNode "app" [_, _, f, _]) = go (count + 1) f
    go count (TemplateNode symbol [_]) = Just (symbol, count)
    go _ _ = Nothing

-- | Read a known raw program spine. Holes and recursion cannot fix a key.
partialSpine :: PartialTerm -> Maybe SpineKey
partialSpine = go 0
  where
    go count (CT.Node (ConcreteSymbol "app") [_, _, f, _]) = go (count + 1) f
    go count (CT.Node (ConcreteSymbol symbol) [_]) = Just (symbol, count)
    go _ _ = Nothing

-- | Resume the parts whose holes now have the expanded representative.
resume :: UVar -> PartialTerm -> Pending -> EnumerateM Symbol (Maybe Pending)
resume current partial pending = fmap (fmap concat . sequence) (traverse part pending)
  where
    part (template, uv) = do
        representative <- getUVarRepresentative uv
        pure $
            if representative == current
                then matchPartial template partial
                else Just [(template, representative)]

{- | Match a partial term. Nothing rejects the match. An empty list proves
the match. A nonempty list records the parts that still need expansion.
-}
matchPartial :: Template Symbol -> PartialTerm -> Maybe Pending
matchPartial Hole _ = Just []
matchPartial (AnyPrefix []) _ = Just []
matchPartial template (CT.Node (UVarHole uv) []) = Just [(template, uv)]
matchPartial _ (CT.Node TruncatedRecursion _) = Nothing
matchPartial template (CT.Node (ConcreteSymbol symbol) children) = case template of
    AnyNode parts -> exact parts
    TemplateNode expected parts | expected == symbol -> exact parts
    AnyPrefix parts -> prefix parts
    TemplatePrefix expected parts | expected == symbol -> prefix parts
    _ -> Nothing
  where
    exact parts
        | length parts == length children = concat <$> zipWithM matchPartial parts children
        | otherwise = Nothing
    prefix parts
        | length parts <= length children = concat <$> zipWithM matchPartial parts children
        | otherwise = Nothing
matchPartial _ _ = Nothing

-- | Program applications in a fragment. Type children are not programs.
programs :: PartialTerm -> [PartialTerm]
programs (CT.Node (ConcreteSymbol "filter") [_, term]) = programs term
programs term@(CT.Node (ConcreteSymbol "app") [_, _, f, x]) = term : programs f ++ programs x
programs _ = []

{- | Select application templates whose annotations are wildcards.
Specftacular applications always have the fixed singleton arrow marker.
Its equality endpoint can still be an unresolved UVar during eager descent.
Ignore that marker only under this encoding invariant. The signature guard
disables pruning when a type constructor also has the raw app/4 shape.
-}
structuralTemplate :: Template Symbol -> Maybe (Template Symbol)
structuralTemplate template@(TemplateNode "app" [_, _, _, _]) = program template
  where
    program Hole = Just Hole
    program (TemplateNode "app" [Hole, marker, function, argument])
        | marker `elem` [Hole, TemplateNode "(->)" []] =
            (\f x -> TemplateNode "app" [Hole, Hole, f, x]) <$> program function <*> program argument
    program (TemplateNode symbol [Hole]) = Just (TemplateNode symbol [Hole])
    program _ = Nothing
structuralTemplate _ = Nothing

{- | View the immutable fragment without reading or expanding any UVar.
The existing lazy term children leave wildcard positions unevaluated.
-}
fragmentTerm :: TermFragment Symbol -> PartialTerm
fragmentTerm (TermFragmentNode symbol children) = CT.Node (ConcreteSymbol symbol) (map fragmentTerm children)
fragmentTerm (TermFragmentUVar uv) = CT.Node (UVarHole uv) []
