-- | Editable source graphs with named productions and removable facts.
module Data.CFTA.Document (
    Annotation (..),
    Document,
    DocumentError (..),
    Edit (..),
    Patch,
    mkDocument,
    fromGraph,
    sourceGraph,
    compileGraph,
    patch,
    applyPatch,
    applyEdits,
    explainDocumentError,
) where

import Control.Monad (foldM, foldM_)
import Data.Bifunctor (first)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (maybeToList)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, conjoinConstraints, noConstraint)
import Data.CFTA.Symbol (Symbol)

-- | A transition name, unique within its state, and its individual source facts.
data Annotation = Annotation
    { annotationName :: !Text
    , annotationFacts :: !(Map Text Constraint)
    }
    deriving (Eq, Show)

-- | A validated source graph whose facts have not been combined or pruned.
newtype Document state = Document (FTA.FTA state Symbol Annotation)
    deriving (Eq, Show)

-- | A structural error, an invalid edit target, or a patch for another document.
data DocumentError state
    = InvalidGraph !(FTA.FTAError state Symbol)
    | DuplicateState !state
    | DuplicateTransition !state !Text
    | MissingState !state
    | MissingTransition !state !Text
    | MissingFact !state !Text !Text
    | StalePatch
    deriving (Eq, Show)

-- | One edit in an ordered atomic batch. Facts select a state and transition name.
data Edit state
    = SetStart !state
    | PutRow !state ![FTA.Transition state Symbol Annotation]
    | DeleteRow !state
    | PutTransition !state !(FTA.Transition state Symbol Annotation)
    | DefineTransition !state !Text !Symbol ![state]
    | DeleteTransition !state !Text
    | SetFact !state !Text !Text !Constraint
    | RemoveFact !state !Text !Text
    deriving (Eq, Show)

-- | An edit batch and the complete source document on which it was prepared.
data Patch state = Patch !(Document state) ![Edit state]
    deriving (Eq, Show)

-- | Validate graph structure, unique state rows, and transition names within rows.
mkDocument ::
    (Ord state) =>
    state -> [(state, [FTA.Transition state Symbol Annotation])] -> Either (DocumentError state) (Document state)
mkDocument initial rows = do
    foldM_ distinctState Set.empty rows
    graph <- first InvalidGraph $ FTA.mkFTA initial rows
    mapM_ distinctTransitions rows
    pure $ Document graph
  where
    distinctState seen (state, _)
        | Set.member state seen = Left $ DuplicateState state
        | otherwise = Right $ Set.insert state seen

-- | Check that the transitions of one row have distinct names.
distinctTransitions :: (state, [FTA.Transition state Symbol Annotation]) -> Either (DocumentError state) ()
distinctTransitions (state, transitions) = foldM_ distinct Set.empty transitions
  where
    distinct seen transition
        | Set.member name seen = Left $ DuplicateTransition state name
        | otherwise = Right $ Set.insert name seen
      where
        name = annotationName $ FTA.transitionConstraint transition

{- | Import each existing annotation as one fact named @imported@. Transition
names are @t0@, @t1@, and so on within each row. This retains the graph, but
cannot recover separate facts or branches discarded before the import.
-}
fromGraph :: (Ord state) => FTA.PlainFTA state Symbol -> Either (DocumentError state) (Document state)
fromGraph graph =
    mkDocument
        (FTA.initialState graph)
        [ ( state
          , [ transition
                { FTA.transitionConstraint =
                    Annotation (Text.pack $ "t" <> show index) (Map.singleton (Text.pack "imported") $ FTA.transitionConstraint transition)
                }
            | (index, transition) <- zip [0 :: Int ..] transitions
            ]
          )
        | (state, transitions) <- Map.toAscList $ FTA.transitionTable graph
        ]

-- | Inspect the complete source graph, including individual fact names and bodies.
sourceGraph :: Document state -> FTA.FTA state Symbol Annotation
sourceGraph (Document graph) = graph

{- | Conjoin each production's current facts. Keep all states and alternatives,
including false annotations. A single fact retains its syntax unchanged.
This operation does not invoke a solver or prune.
-}
compileGraph :: Document state -> FTA.PlainFTA state Symbol
compileGraph = FTA.mapConstraints combine . sourceGraph
  where
    combine annotation = case Map.elems $ annotationFacts annotation of
        [] -> noConstraint
        firstFact : rest -> foldl' conjoinConstraints firstFact rest

-- | Prepare edits against an exact source snapshot. The snapshot remains available.
patch :: Document state -> [Edit state] -> Patch state
patch = Patch

{- | Apply a batch only to its starting document. A stale snapshot returns an
error. Otherwise the result is that of 'applyEdits'. The check compares the
complete starting document.
-}
applyPatch :: (Ord state) => Patch state -> Document state -> Either (DocumentError state) (Document state)
applyPatch (Patch expected edits) current
    | expected /= current = Left StalePatch
    | otherwise = applyEdits edits current

{- | Apply an ordered batch of edits. An invalid edit returns an error.
SetStart makes a state the initial state; the last SetStart of the batch
applies. SetFact adds or replaces a named fact; RemoveFact and
DeleteRow require their targets to exist. PutTransition replaces a named
production in place or appends a new one. DeleteTransition requires an existing
name and leaves the state row. DefineTransition changes the symbol and children
of an existing production while retaining its facts, or appends a new production
with no facts. Named edits require an existing state and a unique
production name. They resolve their targets at that step
in the sequence. Validate graph references and arities after the complete batch,
so the initial state must have a row only at the end of the batch. Without a
SetStart, the initial state stays the same. The old document is unchanged.

The result replaces the rows that the edits change and shares the other rows
(see 'FTA.replaceRows'). A batch that changes the initial state validates the
whole graph again with 'FTA.mkFTA'. Transition names are checked again only in
the changed rows. It does not reuse count tables or provide a compact
serialized patch.
-}
applyEdits :: (Ord state) => [Edit state] -> Document state -> Either (DocumentError state) (Document state)
applyEdits edits current = do
    rows <- foldM apply (FTA.transitionTable graph) edits
    let changed = Map.fromSet (`Map.lookup` rows) $ Set.fromList $ concatMap editState edits
        start = foldl' (\_ state -> state) (FTA.initialState graph) [state | SetStart state <- edits]
    graph' <-
        first InvalidGraph $
            if start == FTA.initialState graph
                then FTA.replaceRows changed graph
                else FTA.mkFTA start $ Map.toList rows
    mapM_ distinctTransitions [(state, transitions) | (state, Just transitions) <- Map.toList changed]
    pure $ Document graph'
  where
    graph = sourceGraph current
    -- The state whose row the edit changes, if any.
    editState edit = case edit of
        SetStart _ -> []
        PutRow state _ -> [state]
        DeleteRow state -> [state]
        PutTransition state _ -> [state]
        DefineTransition state _ _ _ -> [state]
        DeleteTransition state _ -> [state]
        SetFact state _ _ _ -> [state]
        RemoveFact state _ _ -> [state]
    apply rows edit = case edit of
        SetStart _ -> Right rows
        PutRow state transitions -> Right $ Map.insert state transitions rows
        DeleteRow state
            | Map.member state rows -> Right $ Map.delete state rows
            | otherwise -> Left $ MissingState state
        PutTransition state transition -> case Map.lookup state rows of
            Nothing -> Left $ MissingState state
            Just transitions
                | any (named name) transitions -> changeTransition state name (const $ Right $ Just transition) rows
                | otherwise -> Right $ Map.insert state (transitions <> [transition]) rows
              where
                name = annotationName $ FTA.transitionConstraint transition
        DefineTransition state name symbol children -> case Map.lookup state rows of
            Nothing -> Left $ MissingState state
            Just transitions
                | any (named name) transitions -> changeTransition state name changeConstructor rows
                | otherwise ->
                    Right $ Map.insert state (transitions <> [FTA.Transition symbol children $ Annotation name Map.empty]) rows
              where
                changeConstructor selected = Right $ Just selected{FTA.transitionSymbol = symbol, FTA.transitionChildren = children}
        DeleteTransition state name -> changeTransition state name (const $ Right Nothing) rows
        SetFact state transition fact constraint ->
            changeFacts state transition (Right . Map.insert fact constraint) rows
        RemoveFact state transition fact ->
            changeFacts state transition (remove state transition fact) rows
    remove state transition fact facts
        | Map.member fact facts = Right $ Map.delete fact facts
        | otherwise = Left $ MissingFact state transition fact
    changeFacts state name update = changeTransition state name $ \selected -> do
        let annotation = FTA.transitionConstraint selected
        facts <- update $ annotationFacts annotation
        Right $ Just selected{FTA.transitionConstraint = annotation{annotationFacts = facts}}
    changeTransition state name update rows = case Map.lookup state rows of
        Nothing -> Left $ MissingState state
        Just transitions -> case break (named name) transitions of
            (_, []) -> Left $ MissingTransition state name
            (before, selected : after)
                | any (named name) after -> Left $ DuplicateTransition state name
                | otherwise -> do
                    changed <- update selected
                    Right $ Map.insert state (before <> maybeToList changed <> after) rows
    named name = (== name) . annotationName . FTA.transitionConstraint

-- | Describe an invalid document or edit with its selected state and name.
explainDocumentError :: (Show state) => DocumentError state -> String
explainDocumentError failure = case failure of
    InvalidGraph (FTA.MissingInitialState state) -> "initial state " <> show state <> " has no row"
    InvalidGraph (FTA.DanglingState state) -> "child state " <> show state <> " has no row"
    InvalidGraph (FTA.InconsistentArity symbol expected actual) ->
        "symbol " <> show symbol <> " has arities " <> show expected <> " and " <> show actual
    DuplicateState state -> "duplicate state row: " <> show state
    DuplicateTransition state name -> target state name <> " has a duplicate name"
    MissingState state -> "state " <> show state <> " has no row"
    MissingTransition state name -> target state name <> " does not exist"
    MissingFact state name fact -> target state name <> " has no fact " <> show fact
    StalePatch -> "the document changed after this patch was prepared"
  where
    target state name = "transition " <> show name <> " in state " <> show state
