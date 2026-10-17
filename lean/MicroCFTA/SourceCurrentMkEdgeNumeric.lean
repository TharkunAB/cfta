import MicroCFTA.SourceCurrentAllocatedMkEdge
import MicroCFTA.SourceCurrentEditFrame

/-!
# Initial resources for the actual checked edge constructor

The initial child count bounds either the original edge or the sentinel.
Both returns retain the full checked state and the same inventory Frame.
Raw rejection needs no child computation or stored-field premise.
-/
namespace MicroCFTA.SourceCurrentMkEdgeNumeric
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCapTargetForecast (scalar)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "raw" => SourceEqualityConjoinAllocation.readback
local notation "accepted" => SourceEqualityMkEdgeAllocation.accepted

/-- One initial width bounds the original child list and the rejection sentinel. -/
def finalProfile (count : Nat) (profile : Profile) : Profile :=
  SourceCurrentEditFrame.constructorProfile (max count 1) profile

/-- Construction retains every initial profile component. -/
theorem finalProfile_ge (count : Nat) (profile : Profile) : Le profile (finalProfile count profile) :=
  SourceCurrentEditFrame.constructorProfile_ge _ _

/-- Larger initial resources retain the same constructor forecast. -/
theorem finalProfile_mono (count : Nat) {first last : Profile} (increase : Le first last) :
    Le (finalProfile count first) (finalProfile count last) :=
  SourceCurrentEditFrame.constructorProfile_mono _ increase

/-- A larger initial child count retains the same constructor forecast. -/
theorem finalProfile_count_mono {first last : Nat} (increase : first ≤ last) (profile : Profile) :
    Le (finalProfile first profile) (finalProfile last profile) :=
  SourceCurrentEditFrame.constructorProfile_count_mono (by omega) _

variable {width : Nat}
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem transfer {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {before after : Checked width} {result : EdgeValue Symbol Guard}
    (frame : Frame formulas solver inventory before) (profile : Profile) (fits : Fits profile before)
    (receipt : SourceCurrentAllocatedMkEdge.PhysicalReceipt formulas solver inventory before result after)
    (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard)) (count : Nat)
    (available : Values before.native.machine.heap children) (length : children.length ≤ count)
    (heap : after.native.machine.heap = (run (makeEdge symbol guard children) before.native.machine.heap).2) :
    Frame formulas solver inventory after ∧
      Fits (SourceCurrentEditFrame.constructorProfile count profile) after ∧
      after.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + 1 := by
  have scalarFits : SourceCurrentMemoMergeResourceControl.Fits (scalar profile) before.native.machine.heap :=
    ⟨fits.stored.mono (SourceCurrentConstrainedCapTargetForecast.scalar_mass profile),
      Nat.le_trans fits.nodes (SourceCurrentConstrainedCapTargetForecast.scalar_nodes profile),
      Nat.le_trans fits.edges (SourceCurrentConstrainedCapTargetForecast.scalar_edges profile), Nat.zero_le _⟩
  have resources := SourceCurrentMemoMergeResourceControl.edge symbol guard children before.native.machine.heap
    (scalar profile) count scalarFits available length
  have guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain after.native.machine.heap := by
    rw [heap]
    exact frame.context.guards
  refine ⟨SourceCurrentConstrainedCapOperandFrame.advance frame receipt.ready receipt.extension
    receipt.nodes receipt.edges guards, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [heap]
    exact resources.1.nodes
  · rw [heap]
    exact resources.1.edges
  · rw [receipt.domains]
    exact fits.domains
  · rw [heap]
    exact resources.1.stored
  · rw [heap]
    exact resources.2.2.1
  · rw [heap]
    exact resources.2.2.2

/-- Initial field and child facts construct the full checked edge at the computed profile. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (symbol : Symbol) (constraint : Allocated) (children : List (Value Symbol Guard)) (before : Checked width)
    (frame : Frame formulas solver inventory before) (profile : Profile) (fits : Fits profile before)
    (storedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints constraint.stored)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before.operations (raw constraint))
    (available : Values before.native.machine.heap children) :
    ∃ result after, SourceCurrentAllocatedMkEdge.Receipt formulas solver inventory symbol constraint children before result after ∧
      Frame formulas solver inventory after ∧ Fits (finalProfile children.length profile) after ∧
      after.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + 1 := by
  obtain ⟨result, after, receipt⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver inventory symbol constraint children
    before frame.ready frame.admitted storedReady field available
  have built := SourceEqualityMkEdgeAllocation.build_receipt symbol constraint.stored constraint.guard children
    before.operations before.native.machine.heap frame.ready.good.operations storedReady
  have heap := congrArg (fun output => output.2.native.machine.heap) receipt.actual
  simp only [SourceCurrentAllocatedMkEdge.build] at heap
  rw [built.1] at heap
  change (run (SourceEqualityMkEdgeAllocation.work symbol (raw constraint) children
    (accepted (raw constraint) children.length)) before.native.machine.heap).2 = after.native.machine.heap at heap
  cases keep : accepted (raw constraint) children.length with
  | true =>
      have actual : after.native.machine.heap =
          (run (makeEdge symbol (raw constraint) children) before.native.machine.heap).2 := by
        simpa only [SourceEqualityMkEdgeAllocation.work, keep, ↓reduceIte] using heap.symm
      exact ⟨result, after, receipt, transfer frame profile fits receipt.toPhysicalReceipt symbol (raw constraint)
        children (max children.length 1) available (Nat.le_max_left _ _) actual⟩
  | false =>
      have emptyAvailable : Values before.native.machine.heap ([.empty] : List (Value Symbol Guard)) := by
        intro child member
        cases List.mem_singleton.mp member
        exact InternedProbeProvenance.empty_available _
      have actual : after.native.machine.heap =
          (run (makeEdge symbol top [.empty]) before.native.machine.heap).2 := by
        simpa only [SourceEqualityMkEdgeAllocation.work, keep, Bool.false_eq_true, ↓reduceIte] using heap.symm
      exact ⟨result, after, receipt, transfer frame profile fits receipt.toPhysicalReceipt symbol top [.empty]
        (max children.length 1) emptyAvailable (Nat.le_max_right _ _) actual⟩

/-- Raw rejection constructs its own field and returns the literal sentinel with no child premises. -/
theorem reject (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (symbol : Symbol) (before : Checked width) (frame : Frame formulas solver inventory before)
    (profile : Profile) (fits : Fits profile before) :
    let actual := SourceCurrentAllocatedMkEdge.reject symbol before
    SourceCurrentAllocatedMkEdge.RejectReceipt formulas solver inventory symbol before actual.1 actual.2 ∧
      Frame formulas solver inventory actual.2 ∧ Fits (finalProfile 0 profile) actual.2 ∧
      actual.2.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next ∧
      actual.2.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + 1 := by
  have receipt := SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory symbol before frame.ready frame.admitted
  have available : Values before.native.machine.heap ([.empty] : List (Value Symbol Guard)) := by
    intro child member
    cases List.mem_singleton.mp member
    exact InternedProbeProvenance.empty_available _
  exact ⟨receipt, transfer frame profile fits receipt.toPhysicalReceipt symbol top [.empty] 1 available
    (Nat.le_refl _) rfl⟩

end MicroCFTA.SourceCurrentMkEdgeNumeric
