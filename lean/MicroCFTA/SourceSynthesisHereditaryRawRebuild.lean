import MicroCFTA.SourceSynthesisHereditaryProgramFields
import MicroCFTA.SourceCurrentAllocatedRawRebuild

/-!
# Recursive Program fields at actual raw reconstruction

Raw row construction retains the original full guard and symbol. Its
replacement children supply the new Type and Program certificates.
Unchanged node reconstruction retains the original value. Changed node
reconstruction uses the actual node constructor and its complete row
inputs. Physical effects remain available from the existing raw receipts.
-/
namespace MicroCFTA.SourceSynthesisHereditaryRawRebuild
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisHereditaryProgramFields (ValueFields EdgeFields)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "rawEdge" => SourceCurrentAllocatedRawRebuild.edge
local notation "rawModify" => SourceCurrentAllocatedRawRebuild.modify
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A certified replacement request derives the actual raw row's complete certificate. -/
theorem edge (valid : Guard → Prop) (literal : String → Symbol)
    (original : EdgeValue Symbol Guard) (children : List (Value Symbol Guard)) (before : Checked width)
    (facts : InternedNestedFacts.Facts before.native.machine.heap)
    (available : Values before.native.machine.heap children)
    (request : EdgeFields valid literal (.mk original.entry children)) :
    EdgeFields valid literal (rawEdge original children before).1 := by
  change EdgeFields valid literal
    (run (makeEdge original.entry.key.symbol original.entry.key.constraint children) before.native.machine.heap).1
  exact SourceSynthesisHereditaryProgramFields.makeEdge_fields valid literal
    (.mk original.entry children) before.native.machine.heap facts available request

/-- Actual raw annotation-row work uses its annotated replacement child and original Top guard. -/
theorem edge_annotated (valid : Guard → Prop) (literal : String → Symbol)
    (original : EdgeValue Symbol Guard) (annotation : Value Symbol Guard) (before : Checked width)
    (facts : InternedNestedFacts.Facts before.native.machine.heap)
    (available : Values before.native.machine.heap [annotation])
    (guard : original.entry.key.constraint = top) (typed : Annotated valid annotation) :
    EdgeFields valid literal (rawEdge original [annotation] before).1 :=
  edge valid literal original [annotation] before facts available
    (.annotated (.mk original.entry [annotation]) annotation guard rfl typed)

/-- Actual raw application work derives its certificate from all four replacement operands. -/
theorem edge_application (valid : Guard → Prop) (literal : String → Symbol)
    (original : EdgeValue Symbol Guard) (types marker function argument : Value Symbol Guard)
    (before : Checked width) (facts : InternedNestedFacts.Facts before.native.machine.heap)
    (available : Values before.native.machine.heap [types, marker, function, argument])
    (symbol : original.entry.key.symbol = literal "app")
    (guard : original.entry.key.constraint =
      eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
    (typesTyped : Annotated valid types) (markerTyped : Annotated valid marker)
    (functionFields : ValueFields valid literal function) (argumentFields : ValueFields valid literal argument) :
    EdgeFields valid literal (rawEdge original [types, marker, function, argument] before).1 :=
  edge valid literal original [types, marker, function, argument] before facts available
    (.application (.mk original.entry [types, marker, function, argument]) types marker function argument
      symbol guard rfl typesTyped markerTyped functionFields argumentFields)

/-- Actual raw filter work derives its certificate from the replacement goal and candidate. -/
theorem edge_filter (valid : Guard → Prop) (literal : String → Symbol)
    (original : EdgeValue Symbol Guard) (goal candidates : Value Symbol Guard)
    (before : Checked width) (facts : InternedNestedFacts.Facts before.native.machine.heap)
    (available : Values before.native.machine.heap [goal, candidates])
    (symbol : original.entry.key.symbol = literal "filter")
    (guard : original.entry.key.constraint = eqGuard [[[0], [1, 0]]])
    (goalTyped : Annotated valid goal) (candidateFields : ValueFields valid literal candidates) :
    EdgeFields valid literal (rawEdge original [goal, candidates] before).1 :=
  edge valid literal original [goal, candidates] before facts available
    (.filter (.mk original.entry [goal, candidates]) goal candidates symbol guard rfl goalTyped candidateFields)

/-- Both actual node branches retain recursive fields from their literal construction inputs. -/
theorem modify (valid : Guard → Prop) (literal : String → Symbol)
    (original : Value Symbol Guard) (oldRows newRows : List (EdgeValue Symbol Guard)) (before : Checked width)
    (facts : InternedNestedFacts.Facts before.native.machine.heap)
    (resident : Edges before.native.machine.heap newRows) (originalFields : ValueFields valid literal original)
    (rowFields : ∀ row ∈ newRows, EdgeFields valid literal row) :
    ValueFields valid literal (rawModify original oldRows newRows before).1 := by
  by_cases same : newRows.map (fun row => row.entry.identity) = oldRows.map (fun row => row.entry.identity)
  · simpa only [SourceCurrentAllocatedRawRebuild.modify_unchanged original oldRows newRows before same] using originalFields
  · simpa only [SourceCurrentAllocatedRawRebuild.modify, SourceEqualityPartialNodeRebuild.modify, same, ↓reduceIte] using
      SourceSynthesisHereditaryProgramFields.makeNode_fields valid literal newRows before.native.machine.heap
        facts resident rowFields

end MicroCFTA.SourceSynthesisHereditaryRawRebuild
