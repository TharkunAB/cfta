import MicroCFTA.SourceCurrentSharedParentUniformGuardAlphabet
import MicroCFTA.SourceCurrentAllocatedSharedPartialWorkerStability
import MicroCFTA.SourceCurrentAllocatedSharedPartialCallSteps
import MicroCFTA.SourceCurrentAllocatedSharedPartialEndpointReads
import MicroCFTA.SourceCurrentAllocatedPartialEdgeCall

/-!
# Uniform resources at successful shared outer edge returns

The observed parent return has a canonical receipt at the same endpoint.
The shared graph retains the observed bounds. Its endpoint reads retain
the canonical receipt's own bounds. Stored owners and ready hits retain
the same complete caller. No future body, range or result law is an input.
-/
namespace MicroCFTA.SourceCurrentSharedOuterEdgeGuardAlphabet
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceCurrentAllocatedPartialMemoSound (EdgeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Edge" => EdgeValue Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "UniformReserved" => SourceCurrentSharedParentAlphabetReservation.UniformReserved
local notation "outputProfile" => SourceCurrentSharedParentUniformEnvelope.profile
local notation "outputAlphabet" => SourceCurrentSharedParentUniformGuardAlphabet.forecast
namespace Graph
export SourceCurrentAllocatedSharedPartialGraph (EdgeBody EdgeCall)
export SourceCurrentAllocatedSharedPartialEndpointReads (EdgeBodyReads EdgeCallReads)
end Graph
variable {width bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- A body receipt joins the observed graph and canonical reads at one complete endpoint. -/
structure BodyReceipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (entry : Profile) (budget : Nat) (request : EdgeRequest) (before : Caller width)
    (memos : Memos) (result : Edge) (after : Caller width) (final : Memos) : Prop where
  actual : Graph.EdgeBody budget request before result after
  reads : Graph.EdgeBodyReads formulas solver actual memos final
  semantic : SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver inventory request before result after final
  frame : Frame formulas solver inventory after.checked
  post : Post formulas solver inventory before after final

/-- A call receipt retains the actual owner, final memo bundle and candidate language law. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (entry : Profile) (budget : Nat) (request : EdgeRequest) (before : Caller width)
    (memos : Memos) (result : Edge) (after : Caller width) (final : Memos) : Prop where
  actual : Graph.EdgeCall budget request before result after
  reads : Graph.EdgeCallReads formulas solver actual memos final
  semantic : SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver inventory request before result after final
  frame : Frame formulas solver inventory after.checked
  post : Post formulas solver inventory before after final

/-- Current resources derive the full body receipt at arbitrary successful observed bounds. -/
theorem edge_body
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (alphabet : List Guard) (request : EdgeRequest)
    (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (entry : Profile) (fits : Fits entry before.checked)
    (known : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (uniform : UniformReserved bits budget alphabet entry)
    {f g s r e p h m c n : Nat} {result : Edge} {after : Caller (bits + 2)}
    (observed : SourceCurrentAllocatedSharedPartialWorker.edgeBody f g s r e p h m c n budget request before = .done result after) :
    ∃ next final, BodyReceipt formulas solver next entry budget request before memos result after final ∧
      Fits (outputProfile budget alphabet entry) after.checked ∧
      Carrier (fun guard => guard ∈ outputAlphabet budget alphabet entry) after.checked.native.machine.heap := by
  obtain ⟨checked, fourth, memo, parentDone, rfl⟩ := SourceCurrentAllocatedSharedPartialWorker.edgeBody_done observed
  obtain ⟨loaded, next, final, parent, parentPost, parentFrame, numeric, carrier⟩ :=
    SourceCurrentSharedParentUniformGuardAlphabet.verified formulas solver (request := request) (alphabet := alphabet)
      initial frame entry fits known inherited resident uniform parentDone
  have law : EdgeLaw formulas solver request result := by
    intro ambient term
    have input := InternedGuardedLanguage.edgeMeaning_all (SourceEqualityPCSGuard.holds formulas solver) ambient request.value term
    change InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.value term ↔
      SourceCurrentAllocatedParentEdge.RawMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient
        request.value.entry.key.symbol request.value.entry.key.constraint request.value.children term at input
    exact ⟨fun accepted => input.mpr ((parent.semantic.language ambient term).1 accepted),
      fun satisfied => ((parent.semantic.language ambient term).2 satisfied).trans input.symm⟩
  let actual : Graph.EdgeBody budget request before result (advance before checked fourth memo) :=
    .parent g s r e p h m c n parentDone
  have reads : Graph.EdgeBodyReads formulas solver actual memos final :=
    .parent (g := g) (s := s) (r := r) (e := e) (p := p) (h := h)
      (m := m) (c := c) (n := n) (actual := parentDone) parent
  have semantic : SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result
      (advance before checked fourth memo) final :=
    ⟨parent.semantic.ready, parent.semantic.admitted, parentPost.context.sound, parent.semantic.effects,
      parent.semantic.resident, parent.semantic.stored, parent.semantic.covered, parent.semantic.retained,
      parent.semantic.globals, parent.semantic.correct, parent.semantic.fourthRetained, rfl, law⟩
  exact ⟨next, final, ⟨actual, reads, semantic, parentFrame, parentPost⟩, numeric, carrier⟩

/-- A successful hit or stored-owner evaluation derives its same complete call receipt. -/
theorem edge_call
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (alphabet : List Guard) (request : EdgeRequest)
    (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (entry : Profile) (fits : Fits entry before.checked)
    (known : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (uniform : UniformReserved bits budget alphabet entry)
    {f g s r e p h m c n : Nat} {result : Edge} {after : Caller (bits + 2)}
    (observed : SourceCurrentAllocatedSharedPartialWorker.edgeCall f g s r e p h m c n budget request before = .done result after) :
    ∃ next final, Receipt formulas solver next entry budget request before memos result after final ∧
      Fits (outputProfile budget alphabet entry) after.checked ∧
      Carrier (fun guard => guard ∈ outputAlphabet budget alphabet entry) after.checked.native.machine.heap := by
  rcases started : beginEdge request before with ⟨handle, phase, running⟩
  cases phase with
  | ready value =>
      obtain ⟨same, _, _⟩ := SourceCurrentAllocatedPartialMemoSound.beginEdge_ready_sound formulas solver
        request before initial.sound initial.ready.good.operations.constraints
        initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited resident handle value running started
      obtain ⟨post, available, law⟩ := SourceCurrentAllocatedSharedPartialCallSteps.edge_hit
        formulas solver initial inherited resident started
      subst running
      simp only [SourceCurrentAllocatedSharedPartialWorker.edgeCall, started] at observed
      obtain ⟨sameResult, sameAfter⟩ := SourceCurrentAllocatedSharedPartialWorker.Outcome.done.inj observed
      subst result
      subst after
      have semantic : SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver inventory request before value before memos :=
        ⟨initial.ready, initial.admitted, initial.sound, post.effects, available, initial.stored,
          initial.covered, post.retained, initial.globals, initial.correct, post.fourthRetained, rfl, law⟩
      have enlarged : Le entry (outputProfile budget alphabet entry) :=
        (SourceCurrentInitialSelectionForecast.cover_ge _ _).trans (SourceCurrentMkEdgeNumeric.finalProfile_ge _ _)
      exact ⟨inventory, memos, ⟨.hit started, .hit (started := started), semantic, frame, post⟩, fits.mono enlarged,
        fun key edge found => SourceCurrentSharedParentUniformGuardAlphabet.initial_mem budget alphabet entry (known key edge found)⟩
  | evaluate original =>
      obtain ⟨runningContext, owner, _key, _cell⟩ := SourceCurrentAllocatedSharedPartialCallSteps.edge_start
        formulas solver initial inherited resident started
      have components := beginEdge_components request before
      rw [started] at components
      dsimp only at components
      obtain ⟨checked, _merge, _fourth, nodes⟩ := components
      have runningFrame : Frame formulas solver inventory running.checked := by simpa only [checked] using frame
      have runningFits : Fits entry running.checked := by simpa only [checked] using fits
      have runningKnown : Carrier (fun guard => guard ∈ alphabet) running.checked.native.machine.heap := by
        simpa only [checked] using known
      simp only [SourceCurrentAllocatedSharedPartialWorker.edgeCall, started] at observed
      obtain ⟨value, middle, bodyDone, last⟩ :=
        (SourceCurrentAllocatedSharedPartialWorkerStability.bind_done_iff _ _ _ _).mp observed
      obtain ⟨sameResult, sameAfter⟩ := SourceCurrentAllocatedSharedPartialWorker.Outcome.done.inj last
      subst result
      subst after
      obtain ⟨next, final, body, numeric, carrier⟩ := edge_body formulas solver inventory budget alphabet original
        running memos runningContext runningFrame entry runningFits runningKnown owner.inherited owner.input uniform bodyDone
      obtain ⟨post, available, law⟩ := SourceCurrentAllocatedSharedPartialCallSteps.edge_finish
        formulas solver initial inherited resident started body.actual body.post body.semantic.resident body.semantic.language
      have semantic : SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before value
          (finishEdge handle value middle) final :=
        ⟨post.context.ready, post.context.admitted, post.context.sound, post.effects, available, post.context.stored,
          post.context.covered, post.retained, post.context.globals, post.context.correct, post.fourthRetained,
          body.semantic.nodes.trans nodes, law⟩
      exact ⟨next, final, ⟨.evaluate started body.actual, .evaluate (started := started) body.reads, semantic, body.frame, post⟩, numeric, carrier⟩
  | busy | absent =>
      simp only [SourceCurrentAllocatedSharedPartialWorker.edgeCall, started] at observed
      cases observed

end MicroCFTA.SourceCurrentSharedOuterEdgeGuardAlphabet
