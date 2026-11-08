import MicroCFTA.SourceSynthesisJointProgramRequired
import MicroCFTA.SourceSynthesisGuardRegions

/-!
# Source Type routes at the actual Required return

Returned slot classifications supply every application and filter Type
route. Actual precheck and scan receipts select the source records and
derive the annotation-only Required demands. No returned field certificate
is supplied to the source execution laws.

Semantic readiness, costs, availability, closedness, and input annotations
at the actual Scan return remain entry premises. These laws do not replace
that state by a cold state. They do not prove completion, failure-prefix
safety, all reached source roles, or a global resource bound.
-/
namespace MicroCFTA.SourceSynthesisTypeRequiredRoutes
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisTypePathRoles (AnnotationFields annotation_path)
open SourceCurrentHereditaryTypePaths (TypePath ForestPath)
open SourceCurrentHereditaryConstruction (MuStored)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityProjectionGraph (select)

section Generic
variable {Symbol Guard : Type}

private theorem typed_path (valid : Guard → Prop) (values : List (Value Symbol Guard)) (index : Nat)
    (typed : ∀ value, values[index]? = some value → Annotated valid value) (tail : List Int) :
    ForestPath valid ((index : Int) :: tail) values := by
  intro child selected
  exact .annotated tail child (typed child (by simpa [select] using selected))

private theorem fields_path (valid : Guard → Prop) (values : List (Value Symbol Guard)) (index : Nat)
    (fields : ∀ value, values[index]? = some value → AnnotationFields valid value) (tail : List Int) :
    ForestPath valid ((index : Int) :: 0 :: tail) values := by
  intro child selected
  exact annotation_path (fields child (by simpa [select] using selected)) tail

/-- The literal application layout supplies routes from all returned slot classifications. -/
theorem application_paths (valid : Guard → Prop) (assigned : Nat → Prop)
    (values : List (Value Symbol Guard))
    (layout : ¬ assigned 0 ∧ ¬ assigned 1 ∧ assigned 2 ∧ assigned 3)
    (slots : ∀ index value, values[index]? = some value →
      (assigned index → AnnotationFields valid value) ∧ (¬ assigned index → Annotated valid value))
    (path : EqualityNormalize.Path) (region : SourceSynthesisGuardRegions.applicationRegion path) :
    ForestPath valid (path.map Int.ofNat) values := by
  rcases region with first | second | functionPath | argumentPath
  · obtain ⟨tail, rfl⟩ := first
    simpa [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append] using
      typed_path valid values 0 (fun value found => (slots 0 value found).2 layout.1) (tail.map Int.ofNat)
  · obtain ⟨tail, rfl⟩ := second
    simpa [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append] using
      typed_path valid values 1 (fun value found => (slots 1 value found).2 layout.2.1) (tail.map Int.ofNat)
  · obtain ⟨tail, rfl⟩ := functionPath
    simpa [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append] using
      fields_path valid values 2 (fun value found => (slots 2 value found).1 layout.2.2.1) (tail.map Int.ofNat)
  · obtain ⟨tail, rfl⟩ := argumentPath
    simpa [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append] using
      fields_path valid values 3 (fun value found => (slots 3 value found).1 layout.2.2.2) (tail.map Int.ofNat)

/-- The literal filter layout supplies routes from all returned slot classifications. -/
theorem filter_paths (valid : Guard → Prop) (assigned : Nat → Prop)
    (values : List (Value Symbol Guard)) (layout : ¬ assigned 0 ∧ assigned 1)
    (slots : ∀ index value, values[index]? = some value →
      (assigned index → AnnotationFields valid value) ∧ (¬ assigned index → Annotated valid value))
    (path : EqualityNormalize.Path) (region : SourceSynthesisGuardRegions.filterRegion path) :
    ForestPath valid (path.map Int.ofNat) values := by
  rcases region with first | candidatePath
  · obtain ⟨tail, rfl⟩ := first
    simpa [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append] using
      typed_path valid values 0 (fun value found => (slots 0 value found).2 layout.1) (tail.map Int.ofNat)
  · obtain ⟨tail, rfl⟩ := candidatePath
    simpa [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append] using
      fields_path valid values 1 (fun value found => (slots 1 value found).1 layout.2) (tail.map Int.ofNat)
end Generic

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
variable {records kept : List Record} {g s p h n budget : Nat} {values : List Node}
variable {fourth savedFourth : SourceCurrentEmptinessMemo.Memo} {outcome : Option Class}
variable {fuel readFuel : Nat} {results : List Node} {finish : State Symbol Guard}

/-- Actual application Required work derives all selected routes on its literal returned forest. -/
theorem application_requireAll (valid : Guard → Prop) (types function argument : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (scan : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records
      (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth =
        .done (outcome, kept) scanned savedFourth)
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
        exact SourceSynthesisActualSelectedProgramFootprints.application_annotation_only types function argument
          sourceName sourceChildren occurrence receipt scan compiled index assigned found
      obtain ⟨storedAfter, length, slots⟩ := SourceSynthesisJointProgramRequired.requireAll_slots valid
        (fun index => index = 2 ∨ index = 3) actual compiled semantic costs available closed stored typed fields only
      have selected := SourceSynthesisActualSelectedProgramFootprints.selected_regions receipt scan
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
    (scan : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records
      (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth =
        .done (outcome, kept) scanned savedFourth)
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
        exact SourceSynthesisActualSelectedProgramFootprints.filter_annotation_only candidates goal
          sourceName sourceChildren occurrence receipt scan compiled found
      obtain ⟨storedAfter, length, slots⟩ := SourceSynthesisJointProgramRequired.requireAll_slots valid
        (fun index => index = 1) actual compiled semantic costs available closed stored typed fields only
      have selected := SourceSynthesisActualSelectedProgramFootprints.selected_regions receipt scan
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
end MicroCFTA.SourceSynthesisTypeRequiredRoutes
