import MicroCFTA.SourcePruningEnumerationSharedRecursiveReservation
import MicroCFTA.SourcePruningEnumerationSharedReservationMonotonicity

/-!
# Actual shared edge bounds at the recursive schedule

The original child and guard widths bound the actual shared edge cost.
A shorter edge uses the same scheduled seed. Its returned checked state
then fits the planned head endpoint without another native operation.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedRecursiveReservation
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "advance" => SourcePruningEnumerationSharedIncomingReservation.advance
local notation "edgeCost" => SourcePruningEnumerationSharedNativeBranchCompletion.edgeCost
local notation "edgeCount" => SourcePruningEnumerationRecursiveReservation.edgeCount
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
local notation "guardWidth" => SourcePruningEnumerationGuardWidth.width

private theorem traversal_cost_eq (inputs : List (Node × List Suspended)) :
    SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.cost inputs =
      SourcePruningEnumerationTraversalCompletion.cost inputs := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.cost,
        SourcePruningEnumerationTraversalCompletion.cost, ih]

/-- Current child and guard bounds pay the actual shared edge at its original input. -/
theorem edge_cost_le (seed : Seed) (inherited : Nat) (scs : List Suspended) (start : Nat)
    (edge : EdgeValue Symbol Constraint)
    (children : edge.children.length ≤ scalar seed.2)
    (own : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
        tries.length ≤ guardWidth seed.1)
    (length : scs.length ≤ inherited) :
    edgeCost scs start edge ≤ edgeCount seed inherited := by
  have same : edgeCost scs start edge =
      SourcePruningEnumerationNativeBranchCompletion.edgeCost scs start edge := by
    simp only [SourcePruningEnumerationSharedNativeBranchCompletion.edgeCost,
      SourcePruningEnumerationNativeBranchCompletion.edgeCost,
      SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost,
      SourcePruningEnumerationSelectedEdge.cost, traversal_cost_eq]
    rfl
  rw [same]
  exact SourcePruningEnumerationRecursiveReservation.edge_cost_le
    seed inherited scs start edge children own length

/-- The actual shorter head remains inside one original shared schedule. -/
theorem head_padding (seed : Seed) (inherited actualCost : Nat)
    (bounded : actualCost ≤ edgeCount seed inherited) :
    Le (advance seed actualCost).2 (afterHead seed inherited).2 ∧
      (advance seed actualCost).1 ⊆ (afterHead seed inherited).1 :=
  ⟨SourcePruningEnumerationSharedIncomingReservation.advance_count_profile_mono seed bounded,
    SourcePruningEnumerationSharedIncomingReservation.advance_count_alphabet_mono seed bounded⟩

/-- The same actual head caller fits the planned recursive ingress. -/
theorem head_resources {width : Nat} (seed : Seed) (inherited actualCost : Nat)
    (checked : SourceEqualityNativeDemand.State width)
    (cost : actualCost ≤ edgeCount seed inherited)
    (bounded : Fits (advance seed actualCost).2 checked)
    (known : SourceEqualityAnnotationHeap.Heap
      (fun guard => guard ∈ (advance seed actualCost).1) checked.native.machine.heap) :
    Fits (afterHead seed inherited).2 checked ∧
      SourceEqualityAnnotationHeap.Heap
        (fun guard => guard ∈ (afterHead seed inherited).1) checked.native.machine.heap :=
  SourcePruningEnumerationSharedIncomingReservation.resources_at_later_count
    seed cost checked bounded known

end MicroCFTA.SourcePruningEnumerationSharedRecursiveReservation
