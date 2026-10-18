{-# LANGUAGE OverloadedStrings #-}

{- | Reject redundant partial terms during constrained enumeration.
Each suspended check belongs to one branch and resumes when its hole expands.
-}
module Specftacular.Pruning (prunedTerms) where

import Control.Monad (zipWithM)
import Data.CFTA.Equality (
    EnumerateM,
    Node,
    PartialSymbol (..),
    TermFragment (..),
    UVar,
    expandPartialTermFrag,
    getUVarRepresentative,
    runsInterned,
    termsPruneWith,
 )
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Template (Template (..))
import qualified Data.CFTA.Term as CT
import qualified Data.IntMap.Strict as IntMap
import Data.List (find)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, mapMaybe)
import qualified Data.Set as Set

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
