import MicroCFTA.SourceCurrentConjunctionGuardUniverse
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardOwn
import MicroCFTA.SourceCurrentConstrainedCapGeneratedQueryResources

/-!
# Initial numeric bounds for all physical raw guards

The finite initial guard alphabet determines one common bound vector.
Every stored edge satisfies that vector. A resident precheck then derives
its own class and path bounds. Recursive and open children are permitted.
The vector does not bound child-index magnitudes or compiled syntax size.
-/
namespace MicroCFTA.SourceCurrentGuardHeapBounds
open Cache InternedConstructorTemplates InternedNestedFacts
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits Bounds)
open SourceCurrentAllocatedFiniteOrdinaryGuardLimits
open SourceCurrentAllocatedFiniteOrdinaryGuardOwn (classBudget pathDepth classSteps)
variable {Symbol Formula : Type}

/-- Join the computed raw bounds of every guard in a finite initial alphabet. -/
def limits (alphabet : List (SourceSymbolicIndex.Constraint Formula)) : Limits :=
  alphabet.foldr (fun guard rest => join (of_constraint guard) rest) zero

/-- Each actual alphabet member satisfies the computed common vector. -/
theorem alphabet (guards : List (SourceSymbolicIndex.Constraint Formula)) :
    ∀ guard ∈ guards, Bounds (limits guards) guard := by
  induction guards with
  | nil => intro guard member; cases member
  | cons first rest ih =>
      intro guard member
      rcases List.mem_cons.mp member with same | member
      · subst guard
        exact bounds_mono _ (of_constraint_bounds first) (le_join_left _ _)
      · exact bounds_mono _ (ih guard member) (le_join_right _ _)

/-- Coherent initial records derive their common bound without a shape restriction. -/
theorem initial (source : State Symbol (SourceSymbolicIndex.Constraint Formula)) (facts : Facts source) :
    SourceEqualityAnnotationHeap.Heap
      (Bounds (limits (SourceCurrentConjunctionGuardUniverse.guards source))) source := by
  have known := SourceCurrentConjunctionGuardUniverse.initial source facts
  intro key edge found
  exact alphabet _ key.constraint (known key edge found)

section Concrete
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial flat guard bounds construct the precheck and bound each live own record list. -/
theorem resident_complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked width) (frame : Frame formulas solver inventory before)
    (bound : Limits) (known : SourceEqualityAnnotationHeap.Heap (Bounds bound) before.native.machine.heap)
    (edge : EdgeValue Symbol Guard) (resident : InternedEdgeResidency.EdgeResident before.native.machine.heap edge)
    (inherited : EqValue)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited) :
    ∃ loaded own branch,
      SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory edge.entry.key.constraint loaded
        inherited before own branch ∧
      ∀ records, branch = .classes records →
        (SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.Bounds
          (classBudget bound) (pathDepth bound) (records.map SourceEqualityClassOrder.Record.paths) ∧
        records.length ≤ classBudget bound ∧
        (∀ record ∈ records, record.paths.length ≤ classBudget bound) ∧
        (∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ pathDepth bound)) ∧
        classSteps records ≤ 2 * classBudget bound := by
  obtain ⟨loaded, own, branch, receipt⟩ := SourceCurrentAllocatedPrecheck.resident_complete formulas solver inventory
    before frame.ready frame.admitted edge resident inherited inheritedReady
  refine ⟨loaded, own, branch, receipt, ?_⟩
  intro records same
  subst branch
  have bounded : Bounds bound edge.entry.key.constraint := known _ edge resident
  exact ⟨SourceCurrentAllocatedFiniteOrdinaryGuardOwn.receipt receipt bound bounded,
    SourceCurrentAllocatedFiniteOrdinaryGuardOwn.receipt_steps receipt bound bounded⟩

end Concrete
end MicroCFTA.SourceCurrentGuardHeapBounds
