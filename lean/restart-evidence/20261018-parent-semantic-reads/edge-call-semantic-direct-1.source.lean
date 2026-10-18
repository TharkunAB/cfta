import MicroCFTA.SourceCurrentEdgeCallNumeric
import MicroCFTA.SourceCurrentAllocatedPartialWorkerStability

/-!
# Semantic context at actual outer edge returns

Initial numeric support constructs an edge receipt. A literal successful
call excludes the initial busy branch. Successful-return uniqueness aligns
the receipt with the complete observed result and caller state.
-/
namespace MicroCFTA.SourceCurrentActualEdgeCallSemanticReads
open InternedConstructorTemplates
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Initial entry facts derive the full receipt at any successful outer edge return. -/
theorem edge_call
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (request : EdgeRequest) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap request.value)
    (reserved : SourceCurrentEdgeCallNumeric.Reserved bits budget request before profile)
    {f g s r e p h m c n : Nat} {result : EdgeValue Symbol Guard} {after : Caller (bits + 2)}
    (observed : SourceCurrentAllocatedPartialWorker.edgeCall f g s r e p h m c n budget request before =
      .done result after) :
    ∃ next final, SourceCurrentEdgeCallNumeric.Receipt formulas solver next profile budget request before memos
      result after final := by
  rcases SourceCurrentEdgeCallNumeric.finite_or_busy formulas solver inventory budget request before memos
      initial frame profile fits inherited resident reserved with busy | completed
  · obtain ⟨handle, running, _started, failed⟩ := busy
    rw [failed f g s r e p h m c n] at observed
    cases observed
  · obtain ⟨computed, state, next, final, receipt⟩ := completed
    let fuel := SourceCurrentEdgeCallNumeric.fuel budget request before profile
    have done := receipt.run 0 fuel fuel fuel fuel fuel fuel fuel fuel fuel
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    obtain ⟨sameResult, sameState⟩ :=
      SourceCurrentAllocatedPartialWorkerStability.edgeCall_done_unique observed done
    subst computed state
    exact ⟨next, final, receipt⟩

end MicroCFTA.SourceCurrentActualEdgeCallSemanticReads
