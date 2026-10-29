-- | Composable source updates and reversible exclusions over a language value.
module Data.CFTA.Language (
    Language (..),
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
import Data.CFTA.Language.Source (FactName (..), ProductionName (..))
import qualified Data.CFTA.Language.Source as Source
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Template (Exclusion (..), Template)
import qualified Data.CFTA.Template as Template
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | Editable source and named exclusions. Compilation never replaces this source.
data Language state = Language
    { source :: !(Source.Document state)
    , exclusions :: !(Map ExclusionName (Exclusion Symbol))
    }
    deriving (Eq, Show)

-- | The identity of a reversible exclusion.
newtype ExclusionName = ExclusionName {exclusionNameText :: Text}
    deriving (Eq, Ord, Show, IsString)

-- | A stable production name within one source state.
data ProductionRef state = ProductionRef !state !ProductionName
    deriving (Eq, Ord, Show)

-- | One inspectable operation in a reusable update expression.
data Operation state
    = EditSource !(Source.Edit state)
    | Exclude !ExclusionName !(Exclusion Symbol)
    | Restore !ExclusionName
    deriving (Eq, Show)

-- | An ordered update expression. Composition appends operations from left to right.
newtype Update state = Update {operations :: [Operation state]}
    deriving (Eq, Show, Semigroup, Monoid)

-- | An invalid source edit or removal of an absent exclusion.
data UpdateError state
    = InvalidSource !(Source.DocumentError state)
    | MissingExclusion !ExclusionName
    deriving (Eq, Show)

-- | Start with the complete source language and no exclusions.
fromDocument :: Source.Document state -> Language state
fromDocument document = Language document Map.empty

-- | Select a production by source state and name.
at :: state -> ProductionName -> ProductionRef state
at = ProductionRef

{- | Define a constructor at a named production. Change its symbol and children
in place while retaining its facts, or append a new production with no facts.
The state must exist. Use 'require' and 'relax' to change its facts explicitly.
A kept fact can refer to a child that the new production does not have. An
equality on such a child holds for no term.
-}
define :: ProductionRef state -> Symbol -> [state] -> Update state
define (ProductionRef state name) symbol children =
    editSource $ Source.DefineProduction state name symbol children

-- | Remove an existing production. Keep its state even when the row becomes empty.
remove :: ProductionRef state -> Update state
remove (ProductionRef state name) = editSource $ Source.DeleteProduction state name

-- | Add or replace one named fact on an existing production.
require :: ProductionRef state -> FactName -> Constraint -> Update state
require (ProductionRef state name) fact constraint = editSource $ Source.SetFact state name fact constraint

-- | Remove one existing fact. Keep the production and all its other facts.
relax :: ProductionRef state -> FactName -> Update state
relax (ProductionRef state name) fact = editSource $ Source.RemoveFact state name fact

{- | Make a state the initial state. The state must have a row when the
update ends, so one update can add the row and make it the initial state.
-}
start :: state -> Update state
start = editSource . Source.SetStart

-- | Include a checked source edit, such as an atomic state-row change.
editSource :: Source.Edit state -> Update state
editSource edit = Update [EditSource edit]

-- | Exclude exactly this complete term. Match full symbols, including refinements.
wholeTerm :: Term Symbol -> Exclusion Symbol
wholeTerm = AtRoot . exact

-- | Exclude every term that contains this exact subtree.
subterm :: Term Symbol -> Exclusion Symbol
subterm = Anywhere . exact

-- | Convert a complete term to a template without holes.
exact :: Term Symbol -> Template Symbol
exact (Term.Node symbol children) = Template.TemplateNode symbol $ map exact children

-- | Add or replace a named exclusion without changing the source document.
without :: ExclusionName -> Exclusion Symbol -> Update state
without name exclusion = Update [Exclude name exclusion]

-- | Remove an existing exclusion. Other exclusions and source facts still apply.
restore :: ExclusionName -> Update state
restore name = Update [Restore name]

{- | Apply one reusable expression atomically. Resolve source edits in their order
and validate the final source graph. Then resolve exclusions in their order.
The old value remains available on success or failure. This expression has no
expected version. To apply it to a version that changed after it was written,
use 'Data.CFTA.Language.Merge.merge3'.
-}
update :: (Ord state) => Language state -> Update state -> Either (UpdateError state) (Language state)
update before (Update changes) = do
    let edits = [edit | EditSource edit <- changes]
        document = source before
    changedSource <-
        if null edits
            then Right document
            else first InvalidSource $ Source.applyEdits edits document
    changedExclusions <- foldM apply (exclusions before) changes
    pure $ Language changedSource changedExclusions
  where
    apply current operation = case operation of
        EditSource _ -> Right current
        Exclude name exclusion -> Right $ Map.insert name exclusion current
        Restore name
            | Map.member name current -> Right $ Map.delete name current
            | otherwise -> Left $ MissingExclusion name

{- | Compile facts and apply exclusions without changing the retained source:
'Template.excludeAllFTA' of the exclusions and the compiled document.
Compiled state numbers are query identities, not editable source identities.
Use a constraint-aware query route; plain 'FTA.terms' ignores constraints.
Exclusions can increase the graph size. They keep an unambiguous source
unambiguous. It does not make an ambiguous source unambiguous.
-}
compileGraph :: (Ord state) => Language state -> FTA.PlainFTA Int Symbol
compileGraph language =
    numberStates $ Template.excludeAllFTA (Map.elems $ exclusions language) $ Source.compileGraph $ source language

-- | Give states consecutive numbers in their existing ascending order.
numberStates :: (Ord state) => FTA.PlainFTA state Symbol -> FTA.PlainFTA Int Symbol
numberStates graph = FTA.mapStates (numbers Map.!) graph
  where
    numbers = Map.fromList $ zip (FTA.states graph) [0 ..]

-- | Explain a failed update with the relevant source or exclusion identity.
explainUpdateError :: (Show state) => UpdateError state -> String
explainUpdateError failure = case failure of
    InvalidSource error' -> Source.explainDocumentError error'
    MissingExclusion name -> "exclusion " <> show (exclusionNameText name) <> " does not exist"
