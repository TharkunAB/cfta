import MicroCFTA.SourceCurrentParentNumeric
import MicroCFTA.SourceCurrentAllocatedPartialWorker

/-!
# Initial numeric completion of the outer edge body

The actual parent return supplies the source graph, strict reads, and
guarded edge law. Raw rejection does not demand fields or children.
The initial request and stored field determine the numeric reservation.
The body does not consume outer recursion fuel.
-/
namespace MicroCFTA.SourceCurrentEdgeBodyNumeric
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Edge" => EdgeValue Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "fuel" => SourceCurrentParentForecast.residentFuel
namespace Graph
export SourceCurrentAllocatedPartialGraph (EdgeBody)
export SourceCurrentAllocatedPartialSourceReads (EdgeBodyReads)
end Graph
variable {width bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- One actual body retains the complete caller and strict source reads. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (profile : Profile) (budget : Nat) (request : EdgeRequest) (before : Caller width)
    (memos : Memos) (result : Edge) (after : Caller width) (final : Memos) : Prop where
  /-- The source graph contains the actual checked parent return. -/
  actual : Graph.EdgeBody budget request before result after
  /-- Strict global reads belong to the same actual body. -/
  reads : Graph.EdgeBodyReads formulas solver actual memos final
  /-- The complete old receipt retains physical stores and guarded language. -/
  semantic : SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver inventory request before result after final
  /-- The full Frame shares the caller Post inventory. -/
  frame : Frame formulas solver inventory after.checked
  /-- The original initial request bounds the returned checked state. -/
  fits : Fits (SourceCurrentParentForecast.residentProfile budget request before.checked profile) after.checked
  /-- Both outer tables and the complete caller retain their current laws. -/
  post : Post formulas solver inventory before after final
  /-- Outer fuel is arbitrary and all nine lower fuels can increase independently. -/
  run : ∀ f g s r e p h m c n,
    fuel budget request before.checked profile ≤ g → fuel budget request before.checked profile ≤ s →
    fuel budget request before.checked profile ≤ r → fuel budget request before.checked profile ≤ e →
    fuel budget request before.checked profile ≤ p → fuel budget request before.checked profile ≤ h →
    fuel budget request before.checked profile ≤ m → fuel budget request before.checked profile ≤ c →
    fuel budget request before.checked profile ≤ n →
    SourceCurrentAllocatedPartialWorker.edgeBody f g s r e p h m c n budget request before = .done result after

/-- Initial live facts construct the body without a future parent graph or result law. -/
theorem complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (request : EdgeRequest) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (resident : contradictory request.value.entry.key.constraint = false → Resident before.checked.native.machine.heap request.value)
    (inherited : contradictory request.value.entry.key.constraint = false →
      EqReady before.checked.operations.constraints request.inherited)
    (reserved : SourceCurrentParentForecast.residentReserved bits budget request before.checked profile) :
    ∃ result after next final, Receipt formulas solver next profile budget request before memos result after final := by
  obtain ⟨loaded, result, checked, fourth, memo, next, final, parent, numeric, done⟩ :=
    SourceCurrentParentNumeric.resident_complete formulas solver inventory budget request before memos
      initial frame profile fits resident inherited reserved
  have law : SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver request result := by
    intro ambient term
    have input := InternedGuardedLanguage.edgeMeaning_all (SourceEqualityPCSGuard.holds formulas solver) ambient request.value term
    change InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.value term ↔
      SourceCurrentAllocatedParentEdge.RawMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient
        request.value.entry.key.symbol request.value.entry.key.constraint request.value.children term at input
    exact ⟨fun accepted => input.mpr ((parent.semantic.language ambient term).1 accepted),
      fun satisfied => ((parent.semantic.language ambient term).2 satisfied).trans input.symm⟩
  let actual : Graph.EdgeBody budget request before result (advance before checked fourth memo) :=
    .parent parent.field parent.actual
  have reads : Graph.EdgeBodyReads formulas solver actual memos final := .parent (field := parent.field) parent.reads
  have semantic : SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result
      (advance before checked fourth memo) final :=
    ⟨parent.semantic.ready, parent.semantic.admitted, parent.post.context.sound, parent.semantic.effects,
      parent.semantic.resident, parent.semantic.stored, parent.semantic.covered, parent.semantic.retained,
      parent.semantic.globals, parent.semantic.correct, parent.semantic.fourthRetained, rfl, law⟩
  refine ⟨result, advance before checked fourth memo, next, final,
    actual, reads, semantic, parent.frame, numeric, parent.post, ?_⟩
  intro f g s r e p h m c n hg hs hr he hp hh hm hc hn
  have returned := done g s r e p h m c n hg hs hr he hp hh hm hc hn
  simp only [SourceCurrentAllocatedPartialWorker.edgeBody, returned]

end MicroCFTA.SourceCurrentEdgeBodyNumeric
