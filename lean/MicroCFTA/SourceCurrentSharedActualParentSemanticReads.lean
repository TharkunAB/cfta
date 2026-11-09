import MicroCFTA.SourceCurrentSharedEdgeBodyNumeric
import MicroCFTA.SourceCurrentAllocatedSharedPartialWorkerGraph
import MicroCFTA.SourceCurrentAllocatedSharedParentWorkerStability
import MicroCFTA.SourceCurrentAllocatedSharedPartialWorkerStability

/-!
# Semantic Parent reads at observed successful returns

Initial numeric support constructs the semantic receipt. Successful-return
uniqueness identifies its full return with an actual worker observation.
The observed fuels need no comparison with the initial forecast.
Canonical reads retain their own numeric bounds. The observed bounds do
not change those reads. The body adapter uses the actual shared graph.
-/
namespace MicroCFTA.SourceCurrentSharedActualParentSemanticReads
open InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Initial numeric facts derive the full Parent receipt at any literal successful return. -/
theorem parent
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (profile : Profile) (fits : Fits profile before.checked)
    (live : SourceCurrentSharedParentNumeric.LiveInputs original loaded inherited values before)
    (reserved : SourceCurrentSharedParentForecast.Reserved bits budget values.length original loaded inherited before.checked profile)
    {g s r e p h m c n : Nat} {result : EdgeValue Symbol Guard} {after : Checked (bits + 2)}
    {savedFourth : Fourth} {saved : Memo}
    (observed : SourceCurrentAllocatedSharedParentWorker.edge g s r e p h m c n budget symbol original inherited values
      before.checked before.fourth before.merge = .done result after savedFourth saved) :
    ∃ next final, SourceCurrentSharedParentNumeric.Receipt formulas solver next profile budget symbol original loaded
      inherited values before memos result after savedFourth saved final := by
  obtain ⟨computed, state, fourth, memo, next, final, receipt⟩ :=
    SourceCurrentSharedParentNumeric.complete formulas solver inventory budget symbol original loaded inherited values
      before memos initial frame profile fits live reserved
  let bound := SourceCurrentSharedParentForecast.fuel budget values.length original loaded inherited before.checked profile
  have done := receipt.run bound bound bound bound bound bound bound bound bound
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨sameResult, sameState, sameFourth, sameMemo⟩ :=
    SourceCurrentAllocatedSharedParentWorkerStability.edge_done_unique observed done
  subst computed state fourth memo
  exact ⟨next, final, receipt⟩

/-- Initial resident support derives strict body reads and the full receipt at its observed graph. -/
theorem edge_body
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (request : Request) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (resident : contradictory request.value.entry.key.constraint = false → Resident before.checked.native.machine.heap request.value)
    (inherited : contradictory request.value.entry.key.constraint = false →
      SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (reserved : SourceCurrentSharedParentForecast.residentReserved bits budget request before.checked profile)
    {result : EdgeValue Symbol Guard} {after : Caller (bits + 2)}
    (actual : SourceCurrentAllocatedSharedPartialGraph.EdgeBody budget request before result after) :
    ∃ next final, SourceCurrentSharedEdgeBodyNumeric.Receipt formulas solver next profile budget request before memos
      result after final ∧ SourceCurrentAllocatedSharedPartialEndpointReads.EdgeBodyReads formulas solver actual memos final := by
  have bodyDone : ∃ g s r e p h m c n,
      SourceCurrentAllocatedSharedPartialWorker.edgeBody 0 g s r e p h m c n budget request before =
        .done result after := by
    cases actual with
    | parent g s r e p h m c n observed =>
        exact ⟨g, s, r, e, p, h, m, c, n, by
          simp only [SourceCurrentAllocatedSharedPartialWorker.edgeBody, observed]⟩
  obtain ⟨g, s, r, e, p, h, m, c, n, bodyDone⟩ := bodyDone
  obtain ⟨computed, state, next, final, receipt⟩ := SourceCurrentSharedEdgeBodyNumeric.complete formulas solver
    inventory budget request before memos initial frame profile fits resident inherited reserved
  let bound := SourceCurrentSharedParentForecast.residentFuel budget request before.checked profile
  have done := receipt.run 0 bound bound bound bound bound bound bound bound bound
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨sameResult, sameCaller⟩ :=
    SourceCurrentAllocatedSharedPartialWorkerStability.edgeBody_done_unique bodyDone done
  subst computed state
  exact ⟨next, final, receipt, receipt.reads⟩

end MicroCFTA.SourceCurrentSharedActualParentSemanticReads
