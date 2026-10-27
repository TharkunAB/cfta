-- | Composable source updates and reversible exclusions over a language value.
module Data.CFTA.Language (
    Language (..),
    Exclusion (..),
    ProductionName (..),
    FactName (..),
    ExclusionName (..),
    ProductionRef (..),
    Update (..),
    Operation (..),
    UpdateError (..),
    fromDocument,
    at,
    define,
    remove,
    require,
    relax,
    start,
    editSource,
    wholeTerm,
    subterm,
    without,
    restore,
    update,
    compileGraph,
    explainUpdateError,
) where

import Control.Monad (foldM)
import Data.Bifunctor (first)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.String (IsString)
import Data.Text (Text)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint)
import qualified Data.CFTA.Document as Document
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Template (Template)
import qualified Data.CFTA.Template as Template
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | Editable source and named exclusions. Compilation never replaces this source.
data Language state = Language
    { source :: !(Document.Document state)
    , exclusions :: !(Map ExclusionName Exclusion)
    }
    deriving (Eq, Show)

-- | Exclude matching complete terms, or terms with a matching subtree.
data Exclusion
    = AtRoot !(Template Symbol)
    | Anywhere !(Template Symbol)
    deriving (Eq, Ord, Show)

-- | A source production name. Text belongs at the declaration and codec boundary.
newtype ProductionName = ProductionName {productionNameText :: Text}
    deriving (Eq, Ord, Show, IsString)

-- | A named source obligation, distinct from production and exclusion names.
newtype FactName = FactName {factNameText :: Text}
    deriving (Eq, Ord, Show, IsString)

-- | The identity of a reversible exclusion.
newtype ExclusionName = ExclusionName {exclusionNameText :: Text}
    deriving (Eq, Ord, Show, IsString)

-- | A stable production name within one source state.
data ProductionRef state = ProductionRef !state !ProductionName
    deriving (Eq, Ord, Show)

-- | One inspectable operation in a reusable update expression.
data Operation state
    = EditSource !(Document.Edit state)
    | Exclude !ExclusionName !Exclusion
    | Restore !ExclusionName
    deriving (Eq, Show)

-- | An ordered update expression. Composition appends operations from left to right.
newtype Update state = Update {operations :: [Operation state]}
    deriving (Eq, Show, Semigroup, Monoid)

-- | An invalid source edit or removal of an absent exclusion.
data UpdateError state
    = InvalidSource !(Document.DocumentError state)
    | MissingExclusion !ExclusionName
    deriving (Eq, Show)

-- | Start with the complete source language and no exclusions.
fromDocument :: Document.Document state -> Language state
fromDocument document = Language document Map.empty

-- | Select a production by source state and name.
at :: state -> ProductionName -> ProductionRef state
at = ProductionRef

{- | Define a constructor at a named production. Change its symbol and children
in place while retaining its facts, or append a new production with no facts.
The state must exist. Use 'require' and 'relax' to change its facts explicitly.
-}
define :: ProductionRef state -> Symbol -> [state] -> Update state
define (ProductionRef state name) symbol children =
    editSource $ Document.DefineTransition state (productionNameText name) symbol children

-- | Remove an existing production. Keep its state even when the row becomes empty.
remove :: ProductionRef state -> Update state
remove (ProductionRef state name) = editSource $ Document.DeleteTransition state (productionNameText name)

-- | Add or replace one named fact on an existing production.
require :: ProductionRef state -> FactName -> Constraint -> Update state
require (ProductionRef state name) fact constraint = editSource $ Document.SetFact state (productionNameText name) (factNameText fact) constraint

-- | Remove one existing fact. Keep the production and all its other facts.
relax :: ProductionRef state -> FactName -> Update state
relax (ProductionRef state name) fact = editSource $ Document.RemoveFact state (productionNameText name) (factNameText fact)

{- | Make a state the initial state. The state must have a row when the
update ends, so one update can add the row and make it the initial state.
-}
start :: state -> Update state
start = editSource . Document.SetStart

-- | Include a checked source edit, such as an atomic state-row change.
editSource :: Document.Edit state -> Update state
editSource edit = Update [EditSource edit]

-- | Exclude exactly this complete term. Match full symbols, including refinements.
wholeTerm :: Term Symbol -> Exclusion
wholeTerm = AtRoot . exact

-- | Exclude every term that contains this exact subtree.
subterm :: Term Symbol -> Exclusion
subterm = Anywhere . exact

-- | Convert a complete term to a template without holes.
exact :: Term Symbol -> Template Symbol
exact (Term.Node symbol children) = Template.TemplateNode symbol $ map exact children

-- | Add or replace a named exclusion without changing the source document.
without :: ExclusionName -> Exclusion -> Update state
without name exclusion = Update [Exclude name exclusion]

-- | Remove an existing exclusion. Other exclusions and source facts still apply.
restore :: ExclusionName -> Update state
restore name = Update [Restore name]

{- | Apply one reusable expression atomically. Resolve source edits in their order
and validate the final source graph. Then resolve exclusions in their order.
The old value remains available on success or failure. This expression has no
expected version; use a document patch when that check is required.
-}
update :: (Ord state) => Language state -> Update state -> Either (UpdateError state) (Language state)
update before (Update changes) = do
    let edits = [edit | EditSource edit <- changes]
        document = source before
    changedSource <-
        if null edits
            then Right document
            else first InvalidSource $ Document.applyEdits edits document
    changedExclusions <- foldM apply (exclusions before) changes
    pure $ Language changedSource changedExclusions
  where
    apply current operation = case operation of
        EditSource _ -> Right current
        Exclude name exclusion -> Right $ Map.insert name exclusion current
        Restore name
            | Map.member name current -> Right $ Map.delete name current
            | otherwise -> Left $ MissingExclusion name

{- | Compile facts and apply exclusions without changing the retained source.
Compiled state numbers are query identities, not editable source identities.
Use a constraint-aware query route; plain 'FTA.terms' ignores constraints.
Template lowering can increase graph size. It preserves unambiguity when the
source is unambiguous. It does not make an ambiguous source unambiguous.
-}
compileGraph :: (Ord state) => Language state -> FTA.PlainFTA Int Symbol
compileGraph language =
    if null anywhere
        then roots
        else numberStates $ Template.excludeAnywhereFTA anywhere roots
  where
    graph = numberStates $ Document.compileGraph $ source language
    rootPatterns = [template | AtRoot template <- Map.elems $ exclusions language]
    anywhere = [template | Anywhere template <- Map.elems $ exclusions language]
    roots
        | null rootPatterns = graph
        | otherwise = numberStates $ Template.excludeFTA rootPatterns graph

-- | Give states consecutive numbers in their existing ascending order.
numberStates :: (Ord state) => FTA.PlainFTA state Symbol -> FTA.PlainFTA Int Symbol
numberStates graph = FTA.mapStates (numbers Map.!) graph
  where
    numbers = Map.fromList $ zip (FTA.states graph) [0 ..]

-- | Explain a failed update with the relevant source or exclusion identity.
explainUpdateError :: (Show state) => UpdateError state -> String
explainUpdateError failure = case failure of
    InvalidSource error' -> Document.explainDocumentError error'
    MissingExclusion name -> "exclusion " <> show (exclusionNameText name) <> " does not exist"
