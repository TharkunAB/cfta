import MicroCFTA.SourceSynthesisRequiredAnnotationClassPass
import MicroCFTA.SourceSynthesisRequiredAnnotationRetention
import MicroCFTA.SourceSynthesisNativeTypeSharedRequiredPass

/-!
# Ordinary annotation heads from Required through the application class pass

A retained annotation descendant supplies the initial physical shape.
The same Required execution and literal class pass preserve that shape.
The caller supplies the current typed forest and warm state at Scan's return.
This result does not prove that Scan retains a descendant on every branch.
-/
namespace MicroCFTA.SourceSynthesisRequiredAnnotationPreparationPass
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityNeeded (Needed Path build)
open SourceEqualityRequiredPathShape (PrefixShape ChildrenShape requireAll_shape)
open SourceSynthesisRequiredAnnotationClassPass (OrdinaryAt ForestOrdinaryAt AtFunction)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression application)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisTypePathRoles (AnnotationFields)
open SourceEqualityClassOrder (Record)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "initial" => SourceCurrentAllocatedSharedTargetState.initial
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
variable {width : Nat}

private theorem forest_shape
    {index : Nat} {paths : List Path} {descendant : Int} {tail : Path} {values : List Node}
    (shape : match build paths with | .node entries => ChildrenShape entries 0 values)
    (included : (index :: 0 :: descendant :: tail : Path) ∈ paths) :
    ForestOrdinaryAt index [0] values := by
  obtain ⟨roots, operands, annotations, compiled, operandStored, annotationStored, nonempty⟩ :=
    SourceSynthesisRequiredAnnotationRetention.required_annotation_route paths index descendant tail included
  rw [compiled] at shape
  have operandsNonempty : operands ≠ [] := by
    intro empty
    simp only [empty, SourceEqualityNeededMap.lookup] at annotationStored
    cases annotationStored
  intro value found
  have operandShape : PrefixShape (.node operands) value :=
    shape index value _ found (by simpa only [Nat.zero_add] using operandStored)
  have ordinary := operandShape.ordinary operandsNonempty
  cases value with
  | empty => trivial
  | node entry rows depth free =>
      intro row member child stored
      exact (operandShape.child member stored annotationStored).ordinary nonempty
  | reference | union | mu => cases ordinary

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual Required result supplies both the operand head and its annotation head. -/
theorem required_forest
    {fuel readFuel index : Nat} {paths : List Path} {descendant : Int} {tail : Path}
    {values results : List Node} {before after : Heap}
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (ready : SourceEqualityRequiredCache.Ready before) (available : Values before values)
    (closed : ClosedValues values)
    (included : (index :: 0 :: descendant :: tail : Path) ∈ paths) :
    ForestOrdinaryAt index [0] results :=
  forest_shape (requireAll_shape actual ready available closed) included

variable [DecidableEq Symbol] [DecidableEq Node]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {guard : Guard} {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
variable {inherited own : SourceEqualityConstraintAllocation.Value} {before scanned : Checked width}
variable {records kept : List Record} {budget : Nat}
variable {memos final : EndpointMemoGateTrace.Memos} {values middle results : List Node}
variable {fourth savedFourth : SourceCurrentEmptinessMemo.Memo} {outcome : Option EqualityNormalize.Class}
variable {fuel readFuel : Nat} {heap : Heap} {memo saved : Memo} {after : Checked width}

/-- The same selected application derives its input shape and preserves it through the full pass. -/
theorem application (lib : Library) (types function argument : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
    (receipt : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory guard loaded
      inherited before own (.classes records))
    (scan : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records
      (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth outcome kept scanned savedFourth memos final)
    (ready : Ready lib (initial scanned memo))
    (available : Values scanned.native.machine.heap values) (closed : ClosedValues values)
    (typed : ∀ index value, values[index]? = some value → ¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value)
    (fields : ∀ index value, values[index]? = some value → (index = 2 ∨ index = 3) → AnnotationFields (Origin lib) value)
    (required : SourceEqualityRequiredExecution.requireAll fuel readFuel
      (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values scanned.native.machine.heap = .done middle heap)
    (actual : SourceCurrentAllocatedClassPass.Pass kept middle (advanceHeap scanned heap) memo results after saved)
    {descendant : Int} {tail : Path}
    (included : (2 :: 0 :: descendant :: tail : Path) ∈
      SourceEqualitySelectedRequired.paths (kept.map Record.paths)) : AtFunction results := by
  cases compiled : build (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) with
  | node entries =>
      have only : ∀ (index : Nat) children,
          SourceEqualityNeededMap.lookup (index : Int) entries = some (.node children) →
          (index = 2 ∨ index = 3) → SourceCurrentHereditaryProgramRequired.AnnotationOnly children := by
        intro index children found assigned
        exact SourceSynthesisActualSharedSelectedProgramFootprints.application_annotation_only types function argument
          sourceName sourceChildren occurrence receipt scan compiled index assigned found
      obtain ⟨next, _extension, middleAvailable, middleClosed, _length, _slots⟩ :=
        SourceSynthesisNativeTypeRequired.requireAll lib (fun index => index = 2 ∨ index = 3)
          (before := initial scanned memo) required compiled ready available closed typed fields only
      have entry : Ready lib (initial (advanceHeap scanned heap) memo) :=
        SourceSynthesisNativeTypeSharedState.initial lib _ _ next.checked next.costs next.physicalMemo next.typedMemo
      obtain ⟨_stored, _size, selected⟩ :=
        SourceSynthesisSharedTypeRequiredRoutes.application_requireAll (Origin lib) types function argument
          sourceName sourceChildren occurrence receipt scan required ready.checked.semantic ready.costs
          available closed ready.checked.stored.constructors typed fields
      exact SourceSynthesisRequiredAnnotationClassPass.application_pass lib types function argument
        sourceName sourceChildren occurrence receipt scan actual entry middleAvailable middleClosed
        (fun record member => (selected record member).2)
        (required_forest required ready.checked.semantic.ready available closed included)

end MicroCFTA.SourceSynthesisRequiredAnnotationPreparationPass
