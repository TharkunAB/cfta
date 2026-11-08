import MicroCFTA.SourceCurrentParentUniformEnvelope
import MicroCFTA.SourceCurrentAllocatedParentWorkerStability
import MicroCFTA.SourceCurrentAllocatedPartialWorker

/-!
# Initial numerical certificates for an observed Parent return

The uniform envelope constructs one complete Parent return.
Success uniqueness identifies all four returned fields with the observation.
The observation can use any nine stage bounds. It needs no lower-bound proof.
The returned Post contains the current Context for that exact observed state.
Initial Frame, Fits, guard-alphabet membership and uniform reservations stay
explicit. Their derivation from the original request at every reached caller
remains open. These laws do not give range-free or original-input completion.
-/
namespace MicroCFTA.SourceSynthesisObservedParentContext
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentParentAlphabetReservation (UniformReserved)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Initial numerical certificates give the full receipt and Post for the same observed Parent success. -/
theorem parent_post
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (alphabet : List Guard) (request : Request)
    (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (entry : Profile) (fits : Fits entry before.checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (uniform : UniformReserved bits budget alphabet entry)
    {g s r e p h m c n : Nat} {result : EdgeValue Symbol Guard} {after : Checked (bits + 2)}
    {savedFourth : Fourth} {saved : Memo}
    (observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget request.value.entry.key.symbol
      request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge = .done result after savedFourth saved) :
    ∃ loaded next final,
      SourceCurrentParentNumeric.Receipt formulas solver next entry budget request.value.entry.key.symbol
        request.value.entry.key.constraint loaded request.inherited request.value.children before memos
        result after savedFourth saved final ∧
      Fits (SourceCurrentParentUniformEnvelope.profile budget alphabet entry) after ∧
      Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final := by
  obtain ⟨loaded, chosen, reached, fourth, memo, next, final, receipt, numeric, stable⟩ :=
    SourceCurrentParentUniformEnvelope.complete formulas solver inventory budget alphabet request before memos
      initial frame entry fits known inherited resident uniform
  let ceiling := SourceCurrentParentUniformEnvelope.fuel budget alphabet entry
  have canonical := stable ceiling ceiling ceiling ceiling ceiling ceiling ceiling ceiling ceiling
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    SourceCurrentAllocatedParentWorkerStability.edge_done_unique canonical observed
  exact ⟨loaded, next, final, receipt, numeric, receipt.post⟩

/-- The actual outer edge body returns its own Post, numerical frame and common profile bound. -/
theorem edgeBody_post
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (alphabet : List Guard) (request : Request)
    (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (entry : Profile) (fits : Fits entry before.checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (uniform : UniformReserved bits budget alphabet entry)
    {fuel g s r e p h m c n : Nat} {result : EdgeValue Symbol Guard} {after : Caller (bits + 2)}
    (observed : SourceCurrentAllocatedPartialWorker.edgeBody fuel g s r e p h m c n budget request before =
      .done result after) :
    ∃ next final, Post formulas solver next before after final ∧
      Frame formulas solver next after.checked ∧
      Fits (SourceCurrentParentUniformEnvelope.profile budget alphabet entry) after.checked := by
  cases parent : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget request.value.entry.key.symbol
      request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | failed =>
      simp only [SourceCurrentAllocatedPartialWorker.edgeBody, parent] at observed
      cases observed
  | done value checked fourth memo =>
      simp only [SourceCurrentAllocatedPartialWorker.edgeBody, parent] at observed
      cases observed
      obtain ⟨_loaded, next, final, receipt, numeric, post⟩ := parent_post
        formulas solver inventory budget alphabet request before memos initial frame entry fits known
        inherited resident uniform parent
      exact ⟨next, final, post, receipt.frame, numeric⟩

end MicroCFTA.SourceSynthesisObservedParentContext
