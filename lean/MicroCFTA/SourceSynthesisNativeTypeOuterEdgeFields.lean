import MicroCFTA.SourceSynthesisNativeTypeEdgeFieldHistory
import MicroCFTA.SourceSynthesisNativeTypeParentAnnotatedWorker
import MicroCFTA.SourceCurrentAllocatedPartialWorkerActual
import MicroCFTA.SourceCurrentAllocatedPartialCallSteps

/-!
# Conditional mixed fields through actual outer edge calls

Cold publication derives its conditional field certificate from the actual
Parent return. Ready hits use exact physical owner equality. Every edge
outcome retains earlier field history. The same successful call derives
its existing source graph, reads, checks and full caller postcondition.

Context, initial shared Type readiness, profile, incoming field history and
the actual reached range plan remain premises. This does not derive all
reached mixed inputs, node descendant fields, completion or global bounds.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeOuterEdgeFields
open InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceSynthesisNativeTypeEdgeFieldHistory (History EdgeFields)
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentOuterPrefixInvariants (Good EdgeReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "SharedReady" => SourceSynthesisNativeTypeSharedState.Ready
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "initialShared" => SourceCurrentAllocatedSharedTargetState.initial
variable {width : Nat} {lib : Library}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest}
variable {before after : Caller width} {result : Edge}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory} {memos : Memos}

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem context_good (initial : Context formulas solver inventory before memos) : Good before := by
  refine ⟨SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked initial.ready.good)
    initial.ready.semantic initial.ready.costs, initial.stored, initial.probes, ?_, ?_⟩
  · refine ⟨initial.sound.valid.nodes.bounded, ?_, ?_⟩
    · intro key handle found
      obtain ⟨cell, present, linked⟩ := initial.sound.valid.nodes.linked key handle found
      exact ⟨cell, present, linked.2⟩
    · intro handle cell present
      have own := initial.sound.nodes handle cell present
      exact ⟨⟨own.inherited, own.input⟩, fun value returned => (own.returned value returned).1⟩
  · refine ⟨initial.sound.valid.edges.bounded, ?_, ?_⟩
    · intro key handle found
      obtain ⟨cell, present, linked⟩ := initial.sound.valid.edges.linked key handle found
      exact ⟨cell, present, linked.2⟩
    · intro handle cell present
      have own := initial.sound.edges handle cell present
      exact ⟨⟨own.inherited, own.input⟩, fun value returned => (own.returned value returned).1⟩

private theorem edgeBody_tables {output : Outcome Edge width}
    (actual : edgeBody fuel g s r e p h m c n budget request before = output) :
    output.state.edgeResults = before.edgeResults := by
  rw [← actual]
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | done => simp [edgeBody, observed, Outcome.state, advance]
  | failed => simp [edgeBody, observed, Outcome.state, advance]

/-- Every literal Parent outcome retains the complete earlier edge field history. -/
theorem edgeBody_history (history : History lib before) :
    History lib (edgeBody fuel g s r e p h m c n budget request before).state := by
  exact ⟨by rw [edgeBody_tables rfl]; exact history.edges⟩

/-- The actual Parent return proves its conditional field certificate without a publication supplier. -/
theorem edgeBody_fields
    (actual : edgeBody fuel g s r e p h m c n budget request before = .done result after)
    (initial : Context formulas solver inventory before memos)
    (typedState : SharedReady lib (initialShared before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (ready : EdgeReady before request)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.edgeBody fuel g s r e p h m c n budget request before) :
    EdgeFields lib request result := by
  have parentRanges := SourceCurrentAllocatedPartialWorkerRanges.edgeBody_of_done ranges actual
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | failed => simp only [edgeBody, observed] at actual; cases actual
  | done value checked fourth memo =>
      simp only [edgeBody, observed] at actual
      cases actual
      constructor
      · intro types function argument sourceName sourceChildren occurrence _arity closed slots
        obtain ⟨_, _, _, _, _, _, _, _, _, resultClosed, _, coupled, retained⟩ :=
          SourceSynthesisNativeTypeParentWorker.application
            (lib := lib) (formulas := formulas) (solver := solver) (context := initial)
            (ready := typedState) (guards := guards) (inheritedReady := ready.1) (resident := ready.2)
            (ranges := parentRanges) (closed := closed) (types := types) (function := function)
            (argument := argument) (sourceName := sourceName) (sourceChildren := sourceChildren)
            (occurrence := occurrence)
            (typed := fun index child found unassigned => (slots index child found).2 unassigned)
            (fields := fun index child found assigned => (slots index child found).1 assigned) observed
        exact ⟨coupled, resultClosed, retained⟩
      · intro candidates goal sourceName sourceChildren occurrence _arity closed slots
        obtain ⟨_, _, _, _, _, _, _, _, _, resultClosed, _, coupled, retained⟩ :=
          SourceSynthesisNativeTypeParentWorker.filter
            (lib := lib) (formulas := formulas) (solver := solver) (context := initial)
            (ready := typedState) (guards := guards) (inheritedReady := ready.1) (resident := ready.2)
            (ranges := parentRanges) (closed := closed) (candidates := candidates) (goal := goal)
            (sourceName := sourceName) (sourceChildren := sourceChildren) (occurrence := occurrence)
            (typed := fun index child found unassigned => (slots index child found).2 unassigned)
            (fields := fun index child found assigned => (slots index child found).1 assigned) observed
        exact ⟨coupled, resultClosed, retained⟩
      · intro annotation guard children typed closed
        obtain ⟨_, _, _, _, _, symbol, guard, children, retained⟩ :=
          SourceSynthesisNativeTypeParentAnnotatedWorker.annotated lib formulas solver observed initial
            typedState guards ready.1 ready.2 guard children typed closed
        exact ⟨symbol, guard, children, retained⟩

/-- Actual warm and cold edge calls retain conditional fields on every outcome. -/
theorem edgeCall_fields
    (initial : Context formulas solver inventory before memos)
    (typedState : SharedReady lib (initialShared before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (ready : EdgeReady before request) (history : History lib before)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.edgeCall fuel g s r e p h m c n budget request before) :
    History lib (edgeCall fuel g s r e p h m c n budget request before).state ∧
      ∀ output final, edgeCall fuel g s r e p h m c n budget request before = .done output final →
        EdgeFields lib request output := by
  have good := context_good initial
  rcases started : beginEdge request before with ⟨handle, action, running⟩
  have runningHistory := SourceSynthesisNativeTypeEdgeFieldHistory.beginEdge history request
  rw [started] at runningHistory
  dsimp only at runningHistory
  cases action with
  | busy | absent =>
      refine ⟨?_, ?_⟩
      · simpa only [edgeCall, started, Outcome.state] using runningHistory
      · intro output final actual
        simp only [edgeCall, started] at actual
        cases actual
  | ready value =>
      refine ⟨?_, ?_⟩
      · simpa only [edgeCall, started, Outcome.state] using runningHistory
      · intro output final actual
        simp only [edgeCall, started] at actual
        cases actual
        exact (SourceSynthesisNativeTypeEdgeFieldHistory.edge_ready history good ready started).2
  | evaluate owner =>
      obtain ⟨runningContext, ownerFacts, sameKey, found⟩ :=
        SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver initial ready.1 ready.2 started
      have ownerReady : EdgeReady running owner := ⟨ownerFacts.inherited, ownerFacts.input⟩
      have components := beginEdge_components request before
      rw [started] at components
      dsimp only at components
      obtain ⟨checkedSame, mergeSame, _⟩ := components
      have runningTyped : SharedReady lib (initialShared running.checked running.merge) := by
        simpa only [checkedSame, mergeSame] using typedState
      have runningGuards : GuardHeap (Origin lib) running.checked.native.machine.heap := by
        simpa only [checkedSame] using guards
      have ownerBefore : EdgeReady before owner := by
        simpa only [EdgeReady, checkedSame] using ownerReady
      have ownerSame : owner = request :=
        SourceSynthesisProgramMemoRoles.edge_same_key good ownerBefore ready sameKey
      have bodyRanges := SourceCurrentAllocatedPartialWorkerRanges.edgeCall_of_evaluate ranges started
      have bodyHistory := edgeBody_history (fuel := fuel) (g := g) (s := s) (r := r) (e := e)
        (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) (request := owner) runningHistory
      cases body : edgeBody fuel g s r e p h m c n budget owner running with
      | failed fault middle =>
          refine ⟨?_, ?_⟩
          · simpa only [edgeCall, started, body, Outcome.bind, Outcome.state] using bodyHistory
          · intro output final actual
            simp only [edgeCall, started, body, Outcome.bind] at actual
            cases actual
      | done value middle =>
          have middleHistory : History lib middle := by
            simpa only [body, Outcome.state] using bodyHistory
          have foundMiddle : middle.edgeResults.cells handle = some ⟨owner, .evaluating⟩ := by
            have tables : middle.edgeResults = running.edgeResults := edgeBody_tables body
            rw [tables]
            exact found
          have published : EdgeFields lib owner value :=
            edgeBody_fields body runningContext runningTyped runningGuards ownerReady bodyRanges
          have finished := SourceSynthesisNativeTypeEdgeFieldHistory.finishEdge middleHistory foundMiddle published
          refine ⟨?_, ?_⟩
          · simpa only [edgeCall, started, body, Outcome.bind, Outcome.state] using finished
          · intro output final actual
            simp only [edgeCall, started, body, Outcome.bind] at actual
            cases actual
            rw [← ownerSame]
            exact published

/-- The same successful literal call derives source reads, checks, full Post and returned fields. -/
theorem edgeCall_verified_fields
    (initial : Context formulas solver inventory before memos)
    (typedState : SharedReady lib (initialShared before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (ready : EdgeReady before request) (history : History lib before)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.edgeCall fuel g s r e p h m c n budget request before)
    (done : edgeCall fuel g s r e p h m c n budget request before = .done result after) :
    ∃ next final, ∃ graph : SourceCurrentAllocatedPartialGraph.EdgeCall budget request before result after,
      SourceCurrentAllocatedPartialSourceReads.EdgeCallReads formulas solver graph memos final ∧
      SourceCurrentAllocatedPartialChecks.Checks (SourceCurrentAllocatedPartialChecks.edgeCallTrace graph) ∧
      Post formulas solver next before after final ∧
      InternedEdgeResidency.EdgeResident after.checked.native.machine.heap result ∧
      SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver request result ∧
      History lib after ∧ EdgeFields lib request result := by
  obtain ⟨next, final, graph, reads, checks, post, resident, law⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.edgeCall_verified formulas solver initial ready.1 ready.2 ranges done
  have retained := edgeCall_fields initial typedState guards ready history ranges
  have afterHistory : History lib after := by simpa only [done, Outcome.state] using retained.1
  exact ⟨next, final, graph, reads, checks, post, resident, law, afterHistory, retained.2 result after done⟩

end MicroCFTA.SourceSynthesisNativeTypeOuterEdgeFields
