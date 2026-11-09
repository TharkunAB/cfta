import MicroCFTA.SourceSynthesisTypeRequiredRoutes
import MicroCFTA.SourceSynthesisActualSharedSelectedProgramFootprints

/-!
# Type routes after shared Scan and actual Required execution

The shared Scan reads retain the source records and exact scanned state.
The source guard supplies the annotation-only Required demands. Actual
Required execution then supplies every selected route on its result.
No returned fields or future footprint is an input.

Semantic readiness, costs, available closed inputs and conditional Mu
stores are premises at the scanned heap. These laws do not prove Scan or
Required completion, failure-prefix preservation or a driver bound.
-/
namespace MicroCFTA.SourceSynthesisSharedTypeRequiredRoutes
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisTypePathRoles (AnnotationFields)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentHereditaryConstruction (MuStored)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceSynthesisTypeRequiredRoutes (application_paths filter_paths)

section Source
open EqualityNormalize SourceEqualityClassOrder
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression application ofType)
open SourceCurrentAllocatedPrecheck (Receipt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {guard : Guard} {loaded : Allocated} {inherited own : EqValue} {before scanned : Checked width}
variable {records kept : List Record} {budget : Nat} {values : List Node}
variable {fourth savedFourth : SourceCurrentEmptinessMemo.Memo} {outcome : Option Class}
variable {memos final : EndpointMemoGateTrace.Memos}
variable {fuel readFuel : Nat} {results : List Node} {finish : State Symbol Guard}

/-- Actual application Required work derives all selected routes on its literal returned forest. -/
theorem application_requireAll (valid : Guard → Prop) (types function argument : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (scan : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records
      (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth
        outcome kept scanned savedFourth memos final)
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel
      (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values scanned.native.machine.heap = .done results finish)
    (semantic : SemanticReady scanned.native.machine.heap) (costs : CostHeap scanned.native.machine.heap)
    (available : Values scanned.native.machine.heap values) (closed : ClosedValues values)
    (stored : MuStored valid scanned.native.machine.heap)
    (typed : ∀ index value, values[index]? = some value → ¬ (index = 2 ∨ index = 3) → Annotated valid value)
    (fields : ∀ index value, values[index]? = some value → (index = 2 ∨ index = 3) → AnnotationFields valid value) :
    MuStored valid finish ∧ results.length = values.length ∧
      ∀ record ∈ kept, Coherent record ∧ ∀ path ∈ record.paths,
        ForestPath valid (path.map Int.ofNat) results := by
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) with
  | node entries =>
      have only : ∀ (index : Nat) children,
          SourceEqualityNeededMap.lookup (index : Int) entries = some (.node children) →
          (index = 2 ∨ index = 3) → SourceCurrentHereditaryProgramRequired.AnnotationOnly children := by
        intro index children found assigned
        exact SourceSynthesisActualSharedSelectedProgramFootprints.application_annotation_only types function argument
          sourceName sourceChildren occurrence receipt scan compiled index assigned found
      obtain ⟨storedAfter, length, slots⟩ := SourceSynthesisJointProgramRequired.requireAll_slots valid
        (fun index => index = 2 ∨ index = 3) actual compiled semantic costs available closed stored typed fields only
      have selected := SourceSynthesisActualSharedSelectedProgramFootprints.selected_regions receipt scan
        SourceSynthesisGuardRegions.applicationRegion
        (SourceSynthesisGuardRegions.application_guard_endpoints types function argument
          sourceName guard sourceChildren occurrence).2
      refine ⟨storedAfter, length, ?_⟩
      intro record member
      refine ⟨(selected record member).1, ?_⟩
      intro path included
      exact application_paths valid (fun index => index = 2 ∨ index = 3) results
        (by decide) slots path ((selected record member).2 path included)

/-- Actual filter Required work derives all selected routes on its literal returned forest. -/
theorem filter_requireAll (valid : Guard → Prop) (candidates goal : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : ofType candidates goal = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (scan : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records
      (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth
        outcome kept scanned savedFourth memos final)
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel
      (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values scanned.native.machine.heap = .done results finish)
    (semantic : SemanticReady scanned.native.machine.heap) (costs : CostHeap scanned.native.machine.heap)
    (available : Values scanned.native.machine.heap values) (closed : ClosedValues values)
    (stored : MuStored valid scanned.native.machine.heap)
    (typed : ∀ index value, values[index]? = some value → index ≠ 1 → Annotated valid value)
    (fields : ∀ index value, values[index]? = some value → index = 1 → AnnotationFields valid value) :
    MuStored valid finish ∧ results.length = values.length ∧
      ∀ record ∈ kept, Coherent record ∧ ∀ path ∈ record.paths,
        ForestPath valid (path.map Int.ofNat) results := by
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) with
  | node entries =>
      have only : ∀ (index : Nat) children,
          SourceEqualityNeededMap.lookup (index : Int) entries = some (.node children) →
          index = 1 → SourceCurrentHereditaryProgramRequired.AnnotationOnly children := by
        intro index children found assigned
        subst index
        exact SourceSynthesisActualSharedSelectedProgramFootprints.filter_annotation_only candidates goal
          sourceName sourceChildren occurrence receipt scan compiled found
      obtain ⟨storedAfter, length, slots⟩ := SourceSynthesisJointProgramRequired.requireAll_slots valid
        (fun index => index = 1) actual compiled semantic costs available closed stored typed fields only
      have selected := SourceSynthesisActualSharedSelectedProgramFootprints.selected_regions receipt scan
        SourceSynthesisGuardRegions.filterRegion
        (SourceSynthesisGuardRegions.filter_guard_endpoints candidates goal
          sourceName guard sourceChildren occurrence).2
      refine ⟨storedAfter, length, ?_⟩
      intro record member
      refine ⟨(selected record member).1, ?_⟩
      intro path included
      exact filter_paths valid (fun index => index = 1) results
        (by decide) slots path ((selected record member).2 path included)
end Source
end MicroCFTA.SourceSynthesisSharedTypeRequiredRoutes
