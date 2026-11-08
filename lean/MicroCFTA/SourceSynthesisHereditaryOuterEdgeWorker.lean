import MicroCFTA.SourceSynthesisHereditaryClosedMemo
import MicroCFTA.SourceSynthesisNativeTypeAnnotatedParentWorker
import MicroCFTA.SourceSynthesisNativeTypeHereditaryParentWorker
import MicroCFTA.SourceCurrentAllocatedPartialWorkerActual
import MicroCFTA.SourceCurrentAllocatedPartialCallSteps

/-!
# Complete hereditary fields through actual outer edge work

Both memo families retain their captured-owner Type, Program and closedness
certificates. Actual Parent returns prove cold edge publication. Ready hits
transfer the complete stored certificate through exact owner equality.

Classified closed inputs retain the shared Type state and guard profile.
Current Context, initial shared readiness, incoming history and actual
reached range plans remain premises. These laws do not prove all reached
inputs, node descendant preservation, completion or global driver bounds.
-/
namespace MicroCFTA.SourceSynthesisHereditaryOuterEdgeWorker
open InternedConstructorTemplates InternedProbeProvenance
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceSynthesisHereditaryMemoFields (TypeRow)
open SourceSynthesisHereditaryClosedMemo (History EdgeFields)
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentOuterPrefixInvariants (Good EdgeReady)
open SourceRecursiveIntersectionKernel (Extension)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "SharedReady" => SourceSynthesisNativeTypeSharedState.Ready
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "initialShared" => SourceCurrentAllocatedSharedTargetState.initial
variable {width : Nat} {lib : Library} {literal : String → Symbol}
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
    output.state.nodeResults = before.nodeResults ∧ output.state.edgeResults = before.edgeResults := by
  rw [← actual]
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | done => simp [edgeBody, observed, Outcome.state, advance]
  | failed => simp [edgeBody, observed, Outcome.state, advance]

private theorem edgeCall_nodes
    (actual : SourceCurrentAllocatedPartialGraph.EdgeCall budget request before result after) :
    after.nodeResults = before.nodeResults := by
  cases actual with
  | hit started =>
      have components := beginEdge_components request before
      rw [started] at components
      exact components.2.2.2
  | evaluate started body =>
      have components := beginEdge_components request before
      rw [started] at components
      cases body
      exact components.2.2.2

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem receipt_of_post {next final}
    (post : Post formulas solver next before after final)
    (resident : InternedEdgeResidency.EdgeResident after.checked.native.machine.heap result)
    (law : SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver request result)
    (nodes : after.nodeResults = before.nodeResults) :
    SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result after final :=
  ⟨post.context.ready, post.context.admitted, post.context.sound, post.effects, resident,
    post.context.stored, post.context.covered, post.retained, post.context.globals,
    post.context.correct, post.fourthRetained, nodes, law⟩

private theorem edgeBody_post
    (actual : edgeBody fuel g s r e p h m c n budget request before = .done result after)
    (initial : Context formulas solver inventory before memos)
    (typedState : SharedReady lib (initialShared before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (ready : EdgeReady before request)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.edgeBody fuel g s r e p h m c n budget request before)
    (closed : ClosedValues request.value.children)
    (classified : TypeRow lib request.value ∨
      SourceSynthesisHereditaryProgramFields.EdgeFields (Origin lib) literal request.value) :
    SharedReady lib (initialShared after.checked after.merge) ∧
      Extension before.checked.native.machine after.checked.native.machine ∧
      ClosedValues result.children ∧ GuardHeap (Origin lib) after.checked.native.machine.heap := by
  have parentRanges := SourceCurrentAllocatedPartialWorkerRanges.edgeBody_of_done ranges actual
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | failed => simp only [edgeBody, observed] at actual; cases actual
  | done value checked fourth memo =>
      simp only [edgeBody, observed] at actual
      cases actual
      rcases classified with typed | program
      · obtain ⟨_, _, _, _, _, _, next, extension, _, resultClosed, afterGuards, _⟩ :=
          SourceSynthesisNativeTypeAnnotatedParentWorker.edge lib formulas solver observed initial typedState guards
            ready.1 ready.2 parentRanges closed typed
        exact ⟨next, extension, resultClosed, afterGuards⟩
      · obtain ⟨_, _, _, _, _, _, next, extension, _, resultClosed, afterGuards, _⟩ :=
          SourceSynthesisNativeTypeHereditaryParentWorker.edge
            (lib := lib) (literal := literal) (formulas := formulas) (solver := solver)
            (context := initial) (ready := typedState) (guards := guards)
            (inheritedReady := ready.1) (resident := ready.2) (ranges := parentRanges) (closed := closed)
            observed program
        exact ⟨next, extension, resultClosed, afterGuards⟩

/-- Every actual Parent outcome retains both complete outer histories. -/
theorem edgeBody_history (history : History lib literal before) :
    History lib literal (edgeBody fuel g s r e p h m c n budget request before).state := by
  have tables := edgeBody_tables (fuel := fuel) (g := g) (s := s) (r := r) (e := e)
    (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) (request := request) (before := before) rfl
  exact ⟨by rw [tables.1]; exact history.nodes, by rw [tables.2]; exact history.edges⟩

/-- The actual classified Parent return proves every cold publication certificate. -/
theorem edgeBody_fields
    (actual : edgeBody fuel g s r e p h m c n budget request before = .done result after)
    (initial : Context formulas solver inventory before memos)
    (typedState : SharedReady lib (initialShared before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (ready : EdgeReady before request)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.edgeBody fuel g s r e p h m c n budget request before)
    (closed : ClosedValues request.value.children)
    (classified : TypeRow lib request.value ∨
      SourceSynthesisHereditaryProgramFields.EdgeFields (Origin lib) literal request.value) :
    EdgeFields lib literal request result := by
  have post := edgeBody_post actual initial typedState guards ready ranges closed classified
  have parentRanges := SourceCurrentAllocatedPartialWorkerRanges.edgeBody_of_done ranges actual
  refine ⟨?_, fun _ => post.2.2.1⟩
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | failed => simp only [edgeBody, observed] at actual; cases actual
  | done value checked fourth memo =>
      simp only [edgeBody, observed] at actual
      cases actual
      constructor
      · intro typed
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, outputTyped⟩ :=
          SourceSynthesisNativeTypeAnnotatedParentWorker.edge lib formulas solver observed initial typedState guards
            ready.1 ready.2 parentRanges closed typed
        exact outputTyped
      · intro program
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, outputFields⟩ :=
          SourceSynthesisNativeTypeHereditaryParentWorker.edge
            (lib := lib) (literal := literal) (formulas := formulas) (solver := solver)
            (context := initial) (ready := typedState) (guards := guards)
            (inheritedReady := ready.1) (resident := ready.2) (ranges := parentRanges) (closed := closed)
            observed program
        exact outputFields

/-- Actual warm and cold edge calls retain both histories and classified physical posts. -/
theorem edgeCall_fields
    (initial : Context formulas solver inventory before memos)
    (typedState : SharedReady lib (initialShared before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (ready : EdgeReady before request) (history : History lib literal before)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.edgeCall fuel g s r e p h m c n budget request before)
    (closed : ClosedValues request.value.children)
    (classified : TypeRow lib request.value ∨
      SourceSynthesisHereditaryProgramFields.EdgeFields (Origin lib) literal request.value) :
    History lib literal (edgeCall fuel g s r e p h m c n budget request before).state ∧
      ∀ output final, edgeCall fuel g s r e p h m c n budget request before = .done output final →
        EdgeFields lib literal request output ∧ SharedReady lib (initialShared final.checked final.merge) ∧
          Extension before.checked.native.machine final.checked.native.machine ∧ ClosedValues output.children ∧
          GuardHeap (Origin lib) final.checked.native.machine.heap := by
  have good := context_good initial
  rcases started : beginEdge request before with ⟨handle, action, running⟩
  have runningHistory := SourceSynthesisHereditaryClosedMemo.beginEdge history request
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
        have hit := SourceSynthesisHereditaryClosedMemo.edge_ready history good ready started
        refine ⟨hit.2, ?_, ?_, hit.2.closed closed, ?_⟩
        · simpa only [hit.1] using typedState
        · simpa only [hit.1] using Extension.refl before.checked.native.machine
        · simpa only [hit.1] using guards
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
      have ownerBefore : EdgeReady before owner := by simpa only [EdgeReady, checkedSame] using ownerReady
      have ownerSame : owner = request :=
        SourceSynthesisProgramMemoRoles.edge_same_key good ownerBefore ready sameKey
      have ownerClosed : ClosedValues owner.value.children := by simpa only [ownerSame] using closed
      have ownerClassified : TypeRow lib owner.value ∨
          SourceSynthesisHereditaryProgramFields.EdgeFields (Origin lib) literal owner.value := by
        simpa only [ownerSame] using classified
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
          have middleHistory : History lib literal middle := by simpa only [body, Outcome.state] using bodyHistory
          have foundMiddle : middle.edgeResults.cells handle = some ⟨owner, .evaluating⟩ := by
            have tables := (edgeBody_tables body).2
            change middle.edgeResults = running.edgeResults at tables
            rw [tables]
            exact found
          have published := edgeBody_fields body runningContext runningTyped runningGuards ownerReady bodyRanges ownerClosed ownerClassified
          have typedPost := edgeBody_post body runningContext runningTyped runningGuards ownerReady bodyRanges ownerClosed ownerClassified
          have finished := SourceSynthesisHereditaryClosedMemo.finishEdge middleHistory foundMiddle published
          refine ⟨?_, ?_⟩
          · simpa only [edgeCall, started, body, Outcome.bind, Outcome.state] using finished
          · intro output final actual
            simp only [edgeCall, started, body, Outcome.bind] at actual
            cases actual
            have candidateFields : EdgeFields lib literal request value := by simpa only [ownerSame] using published
            refine ⟨candidateFields, ?_, ?_, typedPost.2.2.1, ?_⟩
            · simpa only [finishEdge] using typedPost.1
            · simpa only [finishEdge, checkedSame] using typedPost.2.1
            · simpa only [finishEdge] using typedPost.2.2.2

/-- A successful body retains its same graph, reads, checks, receipt and complete physical post. -/
theorem edgeBody_verified_fields
    (initial : Context formulas solver inventory before memos)
    (typedState : SharedReady lib (initialShared before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (ready : EdgeReady before request)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.edgeBody fuel g s r e p h m c n budget request before)
    (closed : ClosedValues request.value.children)
    (classified : TypeRow lib request.value ∨
      SourceSynthesisHereditaryProgramFields.EdgeFields (Origin lib) literal request.value)
    (done : edgeBody fuel g s r e p h m c n budget request before = .done result after) :
    ∃ next final, ∃ graph : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result after,
      SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads formulas solver graph memos final ∧
      SourceCurrentAllocatedPartialChecks.Checks (SourceCurrentAllocatedPartialChecks.edgeBodyTrace graph) ∧
      SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result after final ∧
      Post formulas solver next before after final ∧
      InternedEdgeResidency.EdgeResident after.checked.native.machine.heap result ∧
      SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver request result ∧
      SharedReady lib (initialShared after.checked after.merge) ∧
      Extension before.checked.native.machine after.checked.native.machine ∧ ClosedValues result.children ∧
      GuardHeap (Origin lib) after.checked.native.machine.heap ∧ EdgeFields lib literal request result := by
  obtain ⟨next, final, graph, reads, checks, post, resident, law⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.edgeBody_verified formulas solver initial ready.1 ready.2 ranges done
  have typedPost := edgeBody_post done initial typedState guards ready ranges closed classified
  exact ⟨next, final, graph, reads, checks, receipt_of_post post resident law (edgeBody_tables done).1,
    post, resident, law, typedPost.1, typedPost.2.1, typedPost.2.2.1, typedPost.2.2.2,
    edgeBody_fields done initial typedState guards ready ranges closed classified⟩

/-- A successful call retains its same graph, reads, checks, receipt, history and complete post. -/
theorem edgeCall_verified_fields
    (initial : Context formulas solver inventory before memos)
    (typedState : SharedReady lib (initialShared before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (ready : EdgeReady before request) (history : History lib literal before)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.edgeCall fuel g s r e p h m c n budget request before)
    (closed : ClosedValues request.value.children)
    (classified : TypeRow lib request.value ∨
      SourceSynthesisHereditaryProgramFields.EdgeFields (Origin lib) literal request.value)
    (done : edgeCall fuel g s r e p h m c n budget request before = .done result after) :
    ∃ next final, ∃ graph : SourceCurrentAllocatedPartialGraph.EdgeCall budget request before result after,
      SourceCurrentAllocatedPartialSourceReads.EdgeCallReads formulas solver graph memos final ∧
      SourceCurrentAllocatedPartialChecks.Checks (SourceCurrentAllocatedPartialChecks.edgeCallTrace graph) ∧
      SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result after final ∧
      Post formulas solver next before after final ∧
      InternedEdgeResidency.EdgeResident after.checked.native.machine.heap result ∧
      SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver request result ∧
      History lib literal after ∧ EdgeFields lib literal request result ∧
      SharedReady lib (initialShared after.checked after.merge) ∧
      Extension before.checked.native.machine after.checked.native.machine ∧ ClosedValues result.children ∧
      GuardHeap (Origin lib) after.checked.native.machine.heap := by
  obtain ⟨next, final, graph, reads, checks, post, resident, law⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.edgeCall_verified formulas solver initial ready.1 ready.2 ranges done
  have retained := edgeCall_fields initial typedState guards ready history ranges closed classified
  have afterHistory : History lib literal after := by simpa only [done, Outcome.state] using retained.1
  obtain ⟨fields, nextReady, extension, resultClosed, afterGuards⟩ := retained.2 result after done
  exact ⟨next, final, graph, reads, checks, receipt_of_post post resident law (edgeCall_nodes graph),
    post, resident, law, afterHistory, fields, nextReady, extension, resultClosed, afterGuards⟩

end MicroCFTA.SourceSynthesisHereditaryOuterEdgeWorker
