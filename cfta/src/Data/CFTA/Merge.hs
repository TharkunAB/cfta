{- | Differences and three-way merges of source documents and languages, by
their stable names.

'diff' gives the update that changes one language into another, and
'diffDocument' gives the patch that changes one document into another. No
edit changes the initial state, so two versions with different initial states
have no difference: the result is 'DifferentStart'.

'merge3' merges two versions of a language, the left and the right, that come
from one base. The keys of the merge are the stable names: the initial state,
the state rows, the production names in a row, the fact names in a
production, and the exclusion names. The symbol and the child states of a
production are one value, and the order of the productions of a row is one
value. For each key:

* When the two sides have the same version, the merge has that version.
* When one side has the version of the base, the merge has the version of the
  other side.
* Otherwise the key is a 'Conflict'.

A key that a version does not have is a version too. Thus a key that one side
deletes and the other side does not change is deleted. A key that one side
deletes and the other side changes is a conflict. A key that both sides add
with the same value is added once, and with different values is a conflict.
A production that the three versions have merges its symbol and children,
then its facts by name. A row that the three versions have merges its
productions by name, then their order.

The order of the productions of a merged row:

1. When the left row has the production names of the base row in the same
   order, the merged row has the order of the right row. The same applies
   with the sides exchanged.
2. When the left row and the right row have the same names in the same
   order, the merged row has that order.
3. Otherwise, the merged row has the names that the base has, in the merge of
   their order on the two sides, then the new names of the left side in the
   left order, then the new names of the right side in the right order. The
   two sides can change the order of the names of the base in different ways:
   that is an 'OrderConflict'.

The order matters: the ranks of a size class follow the order of the rows.

A merge without conflicts can still give an invalid document, for example
when one side deletes a state that a new production of the other side uses.
The result is then 'InvalidMerge'. 'merge3' reports all conflicts, each with
its key and its three versions.

Two documents or languages are the same when they are equal. Equal values
have the same text in the text format of @cfta-serialization@.
-}
module Data.CFTA.Merge (
    Production,
    Versions (..),
    Conflict (..),
    MergeError (..),
    DiffError (..),
    diff,
    diffDocument,
    merge3,
    merge3Document,
) where

import Data.Bifunctor (first)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe)
import qualified Data.Set as Set
import Data.Text (Text)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint)
import qualified Data.CFTA.Document as D
import qualified Data.CFTA.Language as L
import Data.CFTA.Symbol (Symbol)

-- | A production of a source document: its symbol, its child states, and its name and facts.
type Production state = FTA.Transition state Symbol D.Annotation

-- | The three versions of one key in a merge. 'Nothing' when that version does not have the key.
data Versions value = Versions
    { inBase :: !(Maybe value)
    , onLeft :: !(Maybe value)
    , onRight :: !(Maybe value)
    }
    deriving (Eq, Show)

-- | A key that the two sides change in different ways, with its three versions.
data Conflict state
    = -- | The initial state.
      StartConflict !(Versions state)
    | -- | The row of a state that a version does not have.
      RowConflict !state !(Versions [Production state])
    | -- | A production that a version does not have, or whose symbol or child states the two sides change.
      ProductionConflict !(L.ProductionRef state) !(Versions (Production state))
    | -- | A fact of a production.
      FactConflict !(L.ProductionRef state) !L.FactName !(Versions Constraint)
    | -- | The order of the productions of a row: the production names of each version, in order.
      OrderConflict !state !(Versions [L.ProductionName])
    | -- | A named exclusion.
      ExclusionConflict !L.ExclusionName !(Versions L.Exclusion)
    deriving (Eq, Show)

-- | Why two versions do not merge.
data MergeError state
    = -- | The keys that the two sides change in different ways, in key order.
      Conflicts ![Conflict state]
    | -- | The merged keys do not make a valid document.
      InvalidMerge !(D.DocumentError state)
    deriving (Eq, Show)

-- | Why no update changes one version into the other.
data DiffError state
    = -- | The initial states of the two versions. No edit changes the initial state.
      DifferentStart !state !state
    deriving (Eq, Show)

{- | The update that changes the first language into the second:
@update base (diff base other) == Right other@.

The source edits come first, by state in ascending order. A state that only
the first language has is 'D.DeleteRow', and a state that only the second has
is 'D.PutRow'. In a state that both have, a production that only the first
row has is 'D.DeleteTransition'. A production with another symbol or other
child states is 'D.PutTransition', which replaces it in place, and a
production with other facts is 'D.SetFact' and 'D.RemoveFact'. A new
production is 'D.PutTransition', which appends it. These edits keep the order
of the old productions and append the new ones. When the second row has
another order, the edit is one 'D.PutRow' of the second row. Then
'L.Restore' removes each exclusion that only the first language has, and
'L.Exclude' adds or replaces each new or other exclusion.
-}
diff :: (Ord state) => L.Language state -> L.Language state -> Either (DiffError state) (L.Update state)
diff base other = do
    sourceEdits <- edits (L.source base) (L.source other)
    pure $ L.Update $ map L.EditSource sourceEdits <> restored <> excluded
  where
    before = L.exclusions base
    after = L.exclusions other
    restored = [L.Restore name | name <- Map.keys before, Map.notMember name after]
    excluded = [L.Exclude name exclusion | (name, exclusion) <- Map.toAscList after, Map.lookup name before /= Just exclusion]

{- | The patch that changes the first document into the second, with the
source edits of 'diff': @applyPatch (diffDocument base other) base == Right other@.
-}
diffDocument :: (Ord state) => D.Document state -> D.Document state -> Either (DiffError state) (D.Patch state)
diffDocument base other = D.patch base <$> edits base other

-- | The source edits of 'diff'.
edits :: (Ord state) => D.Document state -> D.Document state -> Either (DiffError state) [D.Edit state]
edits base other
    | FTA.initialState before /= FTA.initialState after =
        Left $ DifferentStart (FTA.initialState before) (FTA.initialState after)
    | otherwise = Right $ concatMap stateEdits $ Set.toAscList $ Map.keysSet rowsBefore <> Map.keysSet rowsAfter
  where
    before = D.sourceGraph base
    after = D.sourceGraph other
    rowsBefore = FTA.transitionTable before
    rowsAfter = FTA.transitionTable after
    stateEdits state = case (Map.lookup state rowsBefore, Map.lookup state rowsAfter) of
        (Just _, Nothing) -> [D.DeleteRow state]
        (Nothing, Just row) -> [D.PutRow state row]
        (Just old, Just new)
            | old /= new -> rowEdits state old new
        _ -> []
    rowEdits state old new
        | map productionName new == kept <> added =
            [D.DeleteTransition state name | name <- oldNames, name `notElem` newNames]
                <> concat
                    [ productionEdits state production (named old)
                    | production <- new
                    , productionName production `elem` kept
                    ]
                <> [D.PutTransition state production | production <- new, productionName production `elem` added]
        | otherwise = [D.PutRow state new]
      where
        oldNames = map productionName old
        newNames = map productionName new
        kept = filter (`elem` newNames) oldNames
        added = filter (`notElem` oldNames) newNames
        named row = Map.fromList [(productionName production, production) | production <- row]
    productionEdits state production oldNamed = case Map.lookup name oldNamed of
        Just old
            | constructor old /= constructor production -> [D.PutTransition state production]
            | otherwise ->
                [ D.SetFact state name fact constraint | (fact, constraint) <- Map.toAscList new, Map.lookup fact facts /= Just constraint
                ]
                    <> [D.RemoveFact state name fact | fact <- Map.keys facts, Map.notMember fact new]
          where
            facts = productionFacts old
        Nothing -> []
      where
        name = productionName production
        new = productionFacts production

{- | Merge two versions of a language that come from one base. See the module
documentation for the rules.
-}
merge3 ::
    (Ord state) => L.Language state -> L.Language state -> L.Language state -> Either (MergeError state) (L.Language state)
merge3 base left right = case conflicts of
    [] -> do
        document <- first InvalidMerge $ D.mkDocument start (Map.toAscList rows)
        pure $ L.Language document exclusions
    _ -> Left $ Conflicts conflicts
  where
    graph = D.sourceGraph . L.source
    -- The pairs collect the conflicts in their first component, as a writer does.
    (conflicts, (start, rows, exclusions)) =
        (,,)
            <$> (fromMaybe (FTA.initialState $ graph base) <$> mergeKey StartConflict (initial base) (initial left) (initial right))
            <*> byKey mergeRow (table base) (table left) (table right)
            <*> byKey (\name -> mergeKey (ExclusionConflict name)) (L.exclusions base) (L.exclusions left) (L.exclusions right)
    initial = Just . FTA.initialState . graph
    table = FTA.transitionTable . graph

-- | Merge two versions of a document that come from one base, as 'merge3' does.
merge3Document ::
    (Ord state) => D.Document state -> D.Document state -> D.Document state -> Either (MergeError state) (D.Document state)
merge3Document base left right = L.source <$> merge3 (L.fromDocument base) (L.fromDocument left) (L.fromDocument right)

-- | Merge a row: the productions by name, then their order.
mergeRow ::
    (Eq state) =>
    state ->
    Maybe [Production state] ->
    Maybe [Production state] ->
    Maybe [Production state] ->
    ([Conflict state], Maybe [Production state])
mergeRow state (Just base) (Just left) (Just right) = do
    productions <- byKey mergeProduction (named base) (named left) (named right)
    order <-
        mergeOrder
            state
            (map productionName base)
            (map productionName left)
            (map productionName right)
            (Map.keysSet productions)
    pure $ Just [productions Map.! name | name <- order]
  where
    named row = Map.fromList [(productionName production, production) | production <- row]
    mergeProduction name = mergeProductionAt (L.at state $ L.ProductionName name)
mergeRow state base left right = mergeKey (RowConflict state) base left right

-- | Merge a production: its symbol and child states, then its facts by name.
mergeProductionAt ::
    (Eq state) =>
    L.ProductionRef state ->
    Maybe (Production state) ->
    Maybe (Production state) ->
    Maybe (Production state) ->
    ([Conflict state], Maybe (Production state))
mergeProductionAt ref (Just base) (Just left) (Just right) = do
    (symbol, children) <- case pick (constructor base) (constructor left) (constructor right) of
        Just merged -> pure merged
        Nothing -> ([ProductionConflict ref $ Versions (Just base) (Just left) (Just right)], constructor base)
    facts <- byKey mergeFact (productionFacts base) (productionFacts left) (productionFacts right)
    pure $ Just $ FTA.Transition symbol children $ D.Annotation (D.annotationName $ FTA.transitionConstraint base) facts
  where
    mergeFact name = mergeKey (FactConflict ref $ L.FactName name)
mergeProductionAt ref base left right = mergeKey (ProductionConflict ref) base left right

-- | Merge the order of the production names of a row, and keep the names of the merged productions.
mergeOrder :: state -> [Text] -> [Text] -> [Text] -> Set.Set Text -> ([Conflict state], [Text])
mergeOrder state base left right merged
    | left == base = pure $ present right
    | right == base = pure $ present left
    | left == right = pure $ present left
    | otherwise = case pick (old base) (old left) (old right) of
        Just order -> pure $ order <> present (new left) <> present (filter (`notElem` left) $ new right)
        Nothing -> ([OrderConflict state $ Versions (names base) (names left) (names right)], present left)
  where
    present = filter (`Set.member` merged)
    old = filter (\name -> Set.member name merged && name `elem` base)
    new = filter (`notElem` base)
    names = Just . map L.ProductionName

-- | Merge one key with the rule of the module documentation, or report a conflict and keep the base version.
mergeKey ::
    (Eq value) =>
    (Versions value -> Conflict state) -> Maybe value -> Maybe value -> Maybe value -> ([Conflict state], Maybe value)
mergeKey conflict base left right = case pick base left right of
    Just merged -> pure merged
    Nothing -> ([conflict $ Versions base left right], base)

-- | Merge three maps by key, with a merge of the three versions of each key.
byKey ::
    (Ord key) =>
    (key -> Maybe value -> Maybe value -> Maybe value -> ([Conflict state], Maybe value)) ->
    Map key value ->
    Map key value ->
    Map key value ->
    ([Conflict state], Map key value)
byKey mergeOne base left right =
    Map.fromList . catMaybes <$> traverse one (Set.toAscList $ Map.keysSet base <> Map.keysSet left <> Map.keysSet right)
  where
    one key = fmap (key,) <$> mergeOne key (Map.lookup key base) (Map.lookup key left) (Map.lookup key right)

{- | The merge of one value: the version of the two sides when they agree, or
the version of the side that changes it. 'Nothing' when they change it in
different ways.
-}
pick :: (Eq value) => value -> value -> value -> Maybe value
pick base left right
    | left == right = Just left
    | left == base = Just right
    | right == base = Just left
    | otherwise = Nothing

-- | The name of a production.
productionName :: Production state -> Text
productionName = D.annotationName . FTA.transitionConstraint

-- | The facts of a production.
productionFacts :: Production state -> Map Text Constraint
productionFacts = D.annotationFacts . FTA.transitionConstraint

-- | The symbol and the child states of a production.
constructor :: Production state -> (Symbol, [state])
constructor production = (FTA.transitionSymbol production, FTA.transitionChildren production)
