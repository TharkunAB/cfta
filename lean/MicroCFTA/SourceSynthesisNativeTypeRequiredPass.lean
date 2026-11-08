import MicroCFTA.SourceSynthesisNativeTypeRequired
import MicroCFTA.SourceSynthesisNativeTypeClassPass
import MicroCFTA.SourceSynthesisTypeRequiredRoutes

/-!
# Type routes through Required and the literal class pass

The actual Scan return supplies the entry checked state. Required derives
readiness at its actual returned constructor heap. Only local target slots
reset before the class pass. Native tables and the warm Merge table retain
their derived certificates. Source selection derives every record's routes.

Initial readiness and input classifications at Scan's return remain entry
premises. These laws concern completed Required and pass executions. They
do not prove Scan preservation, completion, failure-prefix safety, all
reached source roles, or a global resource bound.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeRequiredPass
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression application ofType)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisTypePathRoles (AnnotationFields)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentAllocatedPrecheck (Receipt)
open SourceEqualityClassOrder (Record Coherent)
open SourceRecursiveIntersectionKernel (Extension)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "initial" => SourceCurrentAllocatedSharedTargetState.initial
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {guard : Guard} {loaded : Allocated} {inherited own : EqValue} {before scanned : Checked width}
variable {records kept : List Record} {g s p h n budget : Nat} {values middle results : List Node}
variable {fourth savedFourth : SourceCurrentEmptinessMemo.Memo} {outcome : Option EqualityNormalize.Class}
variable {fuel readFuel : Nat} {heap : Heap} {memo saved : Memo} {after : Checked width}

/-- An application pass receives the actual Required forest and its derived warm state. -/
theorem application (lib : Library) (types function argument : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (scan : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records
      (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth =
        .done (outcome, kept) scanned savedFourth)
    (ready : Ready lib (initial scanned memo))
    (available : Values scanned.native.machine.heap values) (closed : ClosedValues values)
    (typed : ∀ index value, values[index]? = some value → ¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value)
    (fields : ∀ index value, values[index]? = some value → (index = 2 ∨ index = 3) → AnnotationFields (Origin lib) value)
    (required : SourceEqualityRequiredExecution.requireAll fuel readFuel
      (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values scanned.native.machine.heap = .done middle heap)
    (actual : SourceCurrentAllocatedClassPass.Pass kept middle (advanceHeap scanned heap) memo results after saved) :
    Ready lib (initial after saved) ∧ Extension scanned.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧
      ∀ record ∈ kept, Coherent record ∧ ∀ path ∈ record.paths,
        ForestPath (Origin lib) (path.map Int.ofNat) results := by
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) with
  | node entries =>
      have only : ∀ (index : Nat) children,
          SourceEqualityNeededMap.lookup (index : Int) entries = some (.node children) →
          (index = 2 ∨ index = 3) → SourceCurrentHereditaryProgramRequired.AnnotationOnly children := by
        intro index children found assigned
        exact SourceSynthesisActualSelectedProgramFootprints.application_annotation_only types function argument
          sourceName sourceChildren occurrence receipt scan compiled index assigned found
      obtain ⟨next, first, middleAvailable, middleClosed, _length, _slots⟩ :=
        SourceSynthesisNativeTypeRequired.requireAll lib (fun index => index = 2 ∨ index = 3)
          (before := initial scanned memo) required compiled ready available closed typed fields only
      have entry : Ready lib (initial (advanceHeap scanned heap) memo) :=
        SourceSynthesisNativeTypeSharedState.initial lib _ _ next.checked next.costs next.physicalMemo next.typedMemo
      obtain ⟨_stored, _size, selected⟩ :=
        SourceSynthesisTypeRequiredRoutes.application_requireAll (Origin lib) types function argument
          sourceName sourceChildren occurrence receipt scan required ready.checked.semantic ready.costs
          available closed ready.checked.stored.constructors typed fields
      obtain ⟨finalReady, last, returned, resultClosed, routes⟩ :=
        SourceSynthesisNativeTypeClassPass.pass lib actual entry middleAvailable middleClosed
          (fun record member => (selected record member).1)
          (fun record member => (selected record member).2)
      refine ⟨finalReady, first.trans last, returned, resultClosed, ?_⟩
      intro record member
      refine ⟨(selected record member).1, ?_⟩
      intro path included
      exact routes (path.map Int.ofNat) ((selected record member).2 path included)

/-- A filter pass receives the actual Required forest and its derived warm state. -/
theorem filter (lib : Library) (candidates goal : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : ofType candidates goal = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (scan : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records
      (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth =
        .done (outcome, kept) scanned savedFourth)
    (ready : Ready lib (initial scanned memo))
    (available : Values scanned.native.machine.heap values) (closed : ClosedValues values)
    (typed : ∀ index value, values[index]? = some value → index ≠ 1 → Annotated (Origin lib) value)
    (fields : ∀ index value, values[index]? = some value → index = 1 → AnnotationFields (Origin lib) value)
    (required : SourceEqualityRequiredExecution.requireAll fuel readFuel
      (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values scanned.native.machine.heap = .done middle heap)
    (actual : SourceCurrentAllocatedClassPass.Pass kept middle (advanceHeap scanned heap) memo results after saved) :
    Ready lib (initial after saved) ∧ Extension scanned.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧
      ∀ record ∈ kept, Coherent record ∧ ∀ path ∈ record.paths,
        ForestPath (Origin lib) (path.map Int.ofNat) results := by
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) with
  | node entries =>
      have only : ∀ (index : Nat) children,
          SourceEqualityNeededMap.lookup (index : Int) entries = some (.node children) →
          index = 1 → SourceCurrentHereditaryProgramRequired.AnnotationOnly children := by
        intro index children found assigned
        subst index
        exact SourceSynthesisActualSelectedProgramFootprints.filter_annotation_only candidates goal
          sourceName sourceChildren occurrence receipt scan compiled found
      obtain ⟨next, first, middleAvailable, middleClosed, _length, _slots⟩ :=
        SourceSynthesisNativeTypeRequired.requireAll lib (fun index => index = 1)
          (before := initial scanned memo) required compiled ready available closed typed fields only
      have entry : Ready lib (initial (advanceHeap scanned heap) memo) :=
        SourceSynthesisNativeTypeSharedState.initial lib _ _ next.checked next.costs next.physicalMemo next.typedMemo
      obtain ⟨_stored, _size, selected⟩ :=
        SourceSynthesisTypeRequiredRoutes.filter_requireAll (Origin lib) candidates goal
          sourceName sourceChildren occurrence receipt scan required ready.checked.semantic ready.costs
          available closed ready.checked.stored.constructors typed fields
      obtain ⟨finalReady, last, returned, resultClosed, routes⟩ :=
        SourceSynthesisNativeTypeClassPass.pass lib actual entry middleAvailable middleClosed
          (fun record member => (selected record member).1)
          (fun record member => (selected record member).2)
      refine ⟨finalReady, first.trans last, returned, resultClosed, ?_⟩
      intro record member
      refine ⟨(selected record member).1, ?_⟩
      intro path included
      exact routes (path.map Int.ofNat) ((selected record member).2 path included)

end MicroCFTA.SourceSynthesisNativeTypeRequiredPass
