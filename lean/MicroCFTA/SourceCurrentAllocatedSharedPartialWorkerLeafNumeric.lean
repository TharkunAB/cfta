import MicroCFTA.SourceCurrentAllocatedSharedPartialWorker
import MicroCFTA.SourceCurrentAllocatedSharedParentWorkerStability
import MicroCFTA.SourceCurrentSharedParentNumeric
import MicroCFTA.SourceCurrentAllocatedPartialCallSteps

/-!
# Actual shared outer leaves from initial invariants

Initial numeric resources construct the shared parent leaf. Successful
observations at other bounds identify the same returned caller. Their
literal graph is separate from the canonical numeric read receipt.
Ready hits retain the actual demand state and skip every parent bound.
These laws do not construct a complete outer recursive execution.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedPartialWorkerLeafNumeric
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw EdgeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "ceiling" => SourceCurrentSharedParentForecast.residentFuel
namespace Graph
export SourceCurrentAllocatedSharedPartialGraph (NodeCall EdgeCall EdgeBody)
end Graph
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width bits : Nat}

/-- Initial current resources construct the shared outer parent leaf at all sufficient bounds. -/
theorem edgeBody_complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (request : EdgeRequest)
    (before : Caller (bits + 2)) (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (resident : contradictory request.value.entry.key.constraint = false → Resident before.checked.native.machine.heap request.value)
    (inherited : contradictory request.value.entry.key.constraint = false → EqReady before.checked.operations.constraints request.inherited)
    (reserved : SourceCurrentSharedParentForecast.residentReserved bits budget request before.checked profile) :
    ∃ loaded result checked fourth memo next final,
      SourceCurrentSharedParentNumeric.Receipt formulas solver next profile budget request.value.entry.key.symbol
        request.value.entry.key.constraint loaded request.inherited request.value.children before memos result checked fourth memo final ∧
      Fits (SourceCurrentSharedParentForecast.residentProfile budget request before.checked profile) checked ∧
      Graph.EdgeBody budget request before result (advance before checked fourth memo) ∧
      ∀ fuel g s r e p h m c n,
        ceiling budget request before.checked profile ≤ g → ceiling budget request before.checked profile ≤ s →
        ceiling budget request before.checked profile ≤ r → ceiling budget request before.checked profile ≤ e →
        ceiling budget request before.checked profile ≤ p → ceiling budget request before.checked profile ≤ h →
        ceiling budget request before.checked profile ≤ m → ceiling budget request before.checked profile ≤ c →
        ceiling budget request before.checked profile ≤ n →
        SourceCurrentAllocatedSharedPartialWorker.edgeBody fuel g s r e p h m c n budget request before =
          .done result (advance before checked fourth memo) := by
  obtain ⟨loaded, result, checked, fourth, memo, next, final, receipt, bounded, run⟩ :=
    SourceCurrentSharedParentNumeric.resident_complete formulas solver inventory budget request before memos initial frame profile fits
      resident inherited reserved
  let f := ceiling budget request before.checked profile
  have done := run f f f f f f f f f (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨loaded, result, checked, fourth, memo, next, final, receipt, bounded,
    .parent f f f f f f f f f done, ?_⟩
  intro fuel g s r e p h m c n hg hs hr he hp hh hm hc hn
  simp only [SourceCurrentAllocatedSharedPartialWorker.edgeBody, run g s r e p h m c n hg hs hr he hp hh hm hc hn]

/-- An observed success has the canonical numeric receipt at its identical endpoint. -/
theorem edgeBody_verified
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest}
    {before after : Caller (bits + 2)} {result : Edge} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (resident : contradictory request.value.entry.key.constraint = false → Resident before.checked.native.machine.heap request.value)
    (inherited : contradictory request.value.entry.key.constraint = false → EqReady before.checked.operations.constraints request.inherited)
    (reserved : SourceCurrentSharedParentForecast.residentReserved bits budget request before.checked profile)
    (observed : SourceCurrentAllocatedSharedPartialWorker.edgeBody fuel g s r e p h m c n budget request before = .done result after) :
    ∃ loaded checked fourth memo next final,
      SourceCurrentSharedParentNumeric.Receipt formulas solver next profile budget request.value.entry.key.symbol
        request.value.entry.key.constraint loaded request.inherited request.value.children before memos result checked fourth memo final ∧
      after = advance before checked fourth memo ∧
      Graph.EdgeBody budget request before result after ∧ Post formulas solver next before after final ∧
      Frame formulas solver next after.checked ∧
      Fits (SourceCurrentSharedParentForecast.residentProfile budget request before.checked profile) after.checked := by
  obtain ⟨checked, fourth, memo, actual, rfl⟩ := SourceCurrentAllocatedSharedPartialWorker.edgeBody_done observed
  obtain ⟨loaded, canonical, reached, savedFourth, saved, next, final, receipt, bounded, run⟩ :=
    SourceCurrentSharedParentNumeric.resident_complete formulas solver inventory budget request before memos initial frame profile fits
      resident inherited reserved
  let f := ceiling budget request before.checked profile
  have done := run f f f f f f f f f (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨rfl, rfl, rfl, rfl⟩ := SourceCurrentAllocatedSharedParentWorkerStability.edge_done_unique actual done
  exact ⟨loaded, checked, fourth, memo, next, final, receipt, rfl,
    .parent g s r e p h m c n actual, receipt.post, receipt.frame, bounded⟩

/-- A ready node uses its exact demand return and requires no recursion or parent bounds. -/
theorem node_ready
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {budget handle : Nat} {request : NodeRequest}
    {before after : Caller width} {result : Node} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (started : beginNode request before = (handle, .ready result, after)) :
    Graph.NodeCall budget request before result after ∧
      SourceCurrentAllocatedSharedPartialWorker.nodeCall 0 0 0 0 0 0 0 0 0 0 budget request before = .done result after ∧
      Post formulas solver inventory before after memos ∧
      Available after.checked.native.machine.heap result ∧ NodeLaw formulas solver request result := by
  obtain ⟨post, available, law⟩ := SourceCurrentAllocatedPartialCallSteps.node_hit formulas solver initial inherited available started
  exact ⟨.hit started, SourceCurrentAllocatedSharedPartialWorker.nodeCall_ready 0 0 0 0 0 0 0 0 0 0
    budget request before after handle result started, post, available, law⟩

/-- A ready edge retains its candidate law and skips every shared parent stage. -/
theorem edge_ready
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {budget handle : Nat} {request : EdgeRequest}
    {before after : Caller width} {result : Edge} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (started : beginEdge request before = (handle, .ready result, after)) :
    Graph.EdgeCall budget request before result after ∧
      SourceCurrentAllocatedSharedPartialWorker.edgeCall 0 0 0 0 0 0 0 0 0 0 budget request before = .done result after ∧
      Post formulas solver inventory before after memos ∧
      Resident after.checked.native.machine.heap result ∧ EdgeLaw formulas solver request result := by
  obtain ⟨post, resident, law⟩ := SourceCurrentAllocatedPartialCallSteps.edge_hit formulas solver initial inherited resident started
  exact ⟨.hit started, SourceCurrentAllocatedSharedPartialWorker.edgeCall_ready 0 0 0 0 0 0 0 0 0 0
    budget request before after handle result started, post, resident, law⟩

end MicroCFTA.SourceCurrentAllocatedSharedPartialWorkerLeafNumeric
