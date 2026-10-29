{- | Differences and three-way merges of source documents and languages, by
their stable names.

'diff' gives the update that changes one language into another, and
'diffDocument' gives the patch that changes one document into another. Both
are total: 'S.SetStart' changes the initial state, so every pair of versions
has a difference.

'merge3' merges two versions of a language, the left and the right, that come
from one base. The keys of the merge are the stable names: the initial state,
the state rows, the production names in a row, the fact names in a
production, and the exclusion names. The symbol and the child states of a
production are one value. For each key:

* When the two sides have the same version, the merge has that version.
* When one side has the version of the base, the merge has the version of the
  other side.
* Otherwise the key is a 'Conflict'.

A key that a version does not have is a version too. Thus a key that one side
deletes and the other side does not change is deleted. A key that one side
deletes and the other side changes is a conflict. A key that both sides add
with the same value is added once, and with different values is a conflict.
A production that the three versions have merges its symbol and children,
then its facts by name. A side that changes the facts of a production wrote
them for its symbol and children. When the merged symbol and children are
other ones, the production is a conflict. A row that the three versions have
merges its productions by name, then their order.

The order of the productions of a merged row:

1. The names that the base and the two sides all have are one key, with the
   rule above. Two different new orders of these names are an
   'OrderConflict'.
2. A new name stays after the name before it on its side: the nearest
   earlier name of step 1, or the start of the row. A deletion on the other
   side does not move it.
3. When the two sides put new names in the same place, and the names of one
   side are in the names of the other side in the same order, the merged row
   has the longer list. When the two sides put different names there, the
   names of each side stay together, and the side with the smaller first
   name comes first. Other new names in the same place are an
   'OrderConflict', and so is a name that the two sides put in different
   places.

The order matters: the ranks of a size class follow the order of the rows.
'merge3' is symmetric: when the sides change places, the result is the same,
or the conflicts are the same with the sides changed.

A merge without conflicts can still give an invalid document, for example
when one side deletes a state that a new production of the other side uses.
The result is then 'InvalidMerge'. 'merge3' reports all conflicts, each with
its key and its three versions.

Two documents or languages are the same when they are equal. Equal values
have the same text in the text format of @cfta-serialization@.
-}
module Data.CFTA.Language.Merge (
    Versions (..),
    Conflict (..),
    MergeError (..),
    diff,
    diffDocument,
    merge3,
    merge3Document,
) where

import Data.Bifunctor (first)
import Data.List (isSubsequenceOf, sort)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, maybeToList)
import qualified Data.Set as Set

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint)
import qualified Data.CFTA.Language as L
import Data.CFTA.Language.Source (FactName, Production, ProductionName)
import qualified Data.CFTA.Language.Source as S
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Template (Exclusion)

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
    | {- | A production that a version does not have, whose symbol or child states
      the two sides change, or whose facts one side changes for other symbol
      and child states.
      -}
      ProductionConflict !(L.ProductionRef state) !(Versions (Production state))
    | -- | A fact of a production.
      FactConflict !(L.ProductionRef state) !FactName !(Versions Constraint)
    | -- | The order of the productions of a row: the production names of each version, in order.
      OrderConflict !state !(Versions [ProductionName])
    | -- | A named exclusion.
      ExclusionConflict !L.ExclusionName !(Versions (Exclusion Symbol))
    deriving (Eq, Show)

-- | Why two versions do not merge.
data MergeError state
    = {- | The keys that the two sides change in different ways: the initial
      state; then each state in ascending order, with its productions by name,
      each before its facts by name, and then the order of its row; then the
      exclusions by name.
      -}
      Conflicts ![Conflict state]
    | -- | The merged keys do not make a valid document.
      InvalidMerge !(S.DocumentError state)
    deriving (Eq, Show)

{- | The update that changes the first language into the second:
@update base (diff base other) == Right other@.

The source edits come first. When the initial states differ, the first edit
is 'S.SetStart'. The other source edits are by state in ascending order. A
state that only the first language has is 'S.DeleteRow', and a state that only
the second has is 'S.PutRow'. In a state that both have, a production that only
the first row has is 'S.DeleteProduction'. A production with another symbol or
other child states is 'S.PutProduction', which replaces it in place, and a
production with other facts is 'S.SetFact' and 'S.RemoveFact'. A new
production is 'S.PutProduction', which appends it. These edits keep the order
of the old productions and append the new ones. When the second row has
another order, the edit is one 'S.PutRow' of the second row. Then
'L.Restore' removes each exclusion that only the first language has, and
'L.Exclude' adds or replaces each new or other exclusion.
-}
diff :: (Ord state) => L.Language state -> L.Language state -> L.Update state
diff base other = L.Update $ map L.EditSource (edits (L.source base) (L.source other)) <> restored <> excluded
  where
    before = L.exclusions base
    after = L.exclusions other
    restored = [L.Restore name | name <- Map.keys before, Map.notMember name after]
    excluded = [L.Exclude name exclusion | (name, exclusion) <- Map.toAscList after, Map.lookup name before /= Just exclusion]

{- | The patch that changes the first document into the second, with the
source edits of 'diff': @applyPatch (diffDocument base other) base == Right other@.
-}
diffDocument :: (Ord state) => S.Document state -> S.Document state -> S.Patch state
diffDocument base other = S.patch base $ edits base other

-- | The source edits of 'diff'.
edits :: (Ord state) => S.Document state -> S.Document state -> [S.Edit state]
edits base other =
    [S.SetStart (FTA.initialState after) | FTA.initialState before /= FTA.initialState after]
        <> concatMap stateEdits (Set.toAscList $ Map.keysSet rowsBefore <> Map.keysSet rowsAfter)
  where
    before = S.sourceGraph base
    after = S.sourceGraph other
    rowsBefore = FTA.transitionTable before
    rowsAfter = FTA.transitionTable after
    stateEdits state = case (Map.lookup state rowsBefore, Map.lookup state rowsAfter) of
        (Just _, Nothing) -> [S.DeleteRow state]
        (Nothing, Just row) -> [S.PutRow state row]
        (Just old, Just new)
            | old /= new -> rowEdits state old new
        _ -> []
    rowEdits state old new
        | map productionName new == kept <> added =
            [S.DeleteProduction state name | name <- oldNames, name `notElem` newNames]
                <> concat
                    [ productionEdits state previous production
                    | production <- new
                    , Just previous <- [Map.lookup (productionName production) (named old)]
                    ]
                <> [S.PutProduction state production | production <- new, productionName production `elem` added]
        | otherwise = [S.PutRow state new]
      where
        oldNames = map productionName old
        newNames = map productionName new
        kept = filter (`elem` newNames) oldNames
        added = filter (`notElem` oldNames) newNames
    productionEdits state previous production
        | constructor previous /= constructor production = [S.PutProduction state production]
        | otherwise =
            [S.SetFact state name fact constraint | (fact, constraint) <- Map.toAscList new, Map.lookup fact old /= Just constraint]
                <> [S.RemoveFact state name fact | fact <- Map.keys old, Map.notMember fact new]
      where
        name = productionName production
        old = productionFacts previous
        new = productionFacts production

{- | Merge two versions of a language that come from one base. See the module
documentation for the rules.
-}
merge3 ::
    (Ord state) => L.Language state -> L.Language state -> L.Language state -> Either (MergeError state) (L.Language state)
merge3 base left right = case conflicts of
    [] -> do
        document <- first InvalidMerge $ S.mkDocument start (Map.toAscList rows)
        pure $ L.Language document exclusions
    _ -> Left $ Conflicts conflicts
  where
    graph = S.sourceGraph . L.source
    -- The pairs collect the conflicts in their first component, as a writer does.
    (conflicts, (start, rows, exclusions)) =
        (,,) . fromMaybe (FTA.initialState $ graph base)
            <$> mergeKey StartConflict (initial base) (initial left) (initial right)
            <*> byKey mergeRow (table base) (table left) (table right)
            <*> byKey (mergeKey . ExclusionConflict) (L.exclusions base) (L.exclusions left) (L.exclusions right)
    initial = Just . FTA.initialState . graph
    table = FTA.transitionTable . graph

-- | Merge two versions of a document that come from one base, as 'merge3' does.
merge3Document ::
    (Ord state) => S.Document state -> S.Document state -> S.Document state -> Either (MergeError state) (S.Document state)
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
    productions <- byKey (mergeProductionAt . L.at state) (named base) (named left) (named right)
    order <-
        mergeOrder
            state
            (map productionName base)
            (map productionName left)
            (map productionName right)
            (Map.keysSet productions)
    pure $ Just [productions Map.! name | name <- order]
mergeRow state base left right = mergeKey (RowConflict state) base left right

{- | Merge a production: its symbol and child states, then its facts by name.
A side that changes the facts must have the merged symbol and child states.
-}
mergeProductionAt ::
    (Eq state) =>
    L.ProductionRef state ->
    Maybe (Production state) ->
    Maybe (Production state) ->
    Maybe (Production state) ->
    ([Conflict state], Maybe (Production state))
mergeProductionAt ref (Just base) (Just left) (Just right) = do
    (symbol, children) <- case pick (constructor base) (constructor left) (constructor right) of
        Just merged | all (factsFor merged) [left, right] -> pure merged
        _ -> ([ProductionConflict ref $ Versions (Just base) (Just left) (Just right)], constructor base)
    facts <- byKey (mergeKey . FactConflict ref) (productionFacts base) (productionFacts left) (productionFacts right)
    pure $ Just $ FTA.Transition symbol children $ S.Annotation (productionName base) facts
  where
    factsFor merged side = productionFacts side == productionFacts base || constructor side == merged
mergeProductionAt ref base left right = mergeKey (ProductionConflict ref) base left right

{- | Merge the order of the production names of a row, with the rules of the
module documentation. The set holds the names of the merged productions.
-}
mergeOrder ::
    state ->
    [ProductionName] ->
    [ProductionName] ->
    [ProductionName] ->
    Set.Set ProductionName ->
    ([Conflict state], [ProductionName])
mergeOrder state base left right merged = case pick (inAll base) (inAll left) (inAll right) of
    Just order
        | Just placed <- concat <$> traverse place (Nothing : map Just order)
        , Set.size (Set.fromList placed) == length placed ->
            pure placed
    _ -> ([OrderConflict state $ Versions (Just base) (Just left) (Just right)], filter (`Set.member` merged) base)
  where
    common name = name `elem` base && name `elem` left && name `elem` right
    inAll = filter common
    -- A name and the new names after it, or the new names at the start.
    place previous = (maybeToList previous <>) <$> together (newAt previous newLeft) (newAt previous newRight)
    newAt = Map.findWithDefault []
    newLeft = newNames left
    newRight = newNames right
    -- The new names of a side, by the nearest earlier name that all three versions have.
    newNames side = Map.fromListWith (flip (<>)) $ go Nothing side
      where
        go _ [] = []
        go before (name : rest)
            | common name = go (Just name) rest
            | name `elem` base = go before rest
            | Set.member name merged = (before, [name]) : go before rest
            | otherwise = go before rest
    -- The new names of the two sides at one place, or 'Nothing' for a conflict.
    together leftNames rightNames
        | leftNames `isSubsequenceOf` rightNames = Just rightNames
        | rightNames `isSubsequenceOf` leftNames = Just leftNames
        | any (`elem` rightNames) leftNames = Nothing
        | otherwise = Just $ concat $ sort [leftNames, rightNames]

-- | Merge one key with the rule of the module documentation, or report a conflict and keep the base version.
mergeKey ::
    (Eq value) =>
    (Versions value -> Conflict state) -> Maybe value -> Maybe value -> Maybe value -> ([Conflict state], Maybe value)
mergeKey conflict base left right = maybe ([conflict $ Versions base left right], base) pure $ pick base left right

-- | Merge three maps by key, with a merge of the three versions of each key.
byKey ::
    (Ord key) =>
    (key -> Maybe value -> Maybe value -> Maybe value -> ([Conflict state], Maybe value)) ->
    Map key value ->
    Map key value ->
    Map key value ->
    ([Conflict state], Map key value)
byKey mergeOne base left right =
    Map.fromDistinctAscList . catMaybes
        <$> traverse one (Set.toAscList $ Map.keysSet base <> Map.keysSet left <> Map.keysSet right)
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

-- | The productions of a row by name.
named :: [Production state] -> Map ProductionName (Production state)
named row = Map.fromList [(productionName production, production) | production <- row]

-- | The name of a production.
productionName :: Production state -> ProductionName
productionName = S.annotationName . FTA.transitionConstraint

-- | The facts of a production.
productionFacts :: Production state -> Map FactName Constraint
productionFacts = S.annotationFacts . FTA.transitionConstraint

-- | The symbol and the child states of a production.
constructor :: Production state -> (Symbol, [state])
constructor production = (FTA.transitionSymbol production, FTA.transitionChildren production)
