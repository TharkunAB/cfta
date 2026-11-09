import MicroCFTA.SourceSynthesisHereditaryClosedMemo
import MicroCFTA.SourceSynthesisNativeTypeAnnotatedSharedParentWorker
import MicroCFTA.SourceSynthesisNativeTypeHereditarySharedParentWorker
import MicroCFTA.SourceCurrentSharedOuterEdgeGuardAlphabet

/-!
# Complete hereditary fields at actual shared outer edge returns

Current resources derive canonical Parent reads at the same observed return.
The actual Parent receipt supplies both conditional field implications.
Cold publication uses its captured owner. Ready hits recover the complete
stored owner certificate. Both outer memo families retain their history.

Current source classifications, closed inputs and one shared reservation
remain premises. These laws do not prove all reached classifications,
worker completion, initial capacity or a complete driver bound.
-/
namespace MicroCFTA.SourceSynthesisHereditarySharedOuterEdgeWorker
open InternedConstructorTemplates InternedProbeProvenance
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceSynthesisHereditaryMemoFields (TypeRow)
open SourceSynthesisHereditaryClosedMemo (History EdgeFields)
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedSharedPartialWorker
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentOuterPrefixInvariants (Good EdgeReady)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceRecursiveIntersectionKernel (Extension)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "SharedReady" => SourceSynthesisNativeTypeSharedState.Ready
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "initialShared" => SourceCurrentAllocatedSharedTargetState.initial
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "UniformReserved" => SourceCurrentSharedParentAlphabetReservation.UniformReserved
local notation "outputProfile" => SourceCurrentSharedParentUniformEnvelope.profile
local notation "outputAlphabet" => SourceCurrentSharedParentUniformGuardAlphabet.forecast
variable {lib : Library} {literal : String → Symbol}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest} {result : Edge}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory} {memos : Memos}

section Core
variable {width : Nat} {before after : Caller width}

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
  cases observed : SourceCurrentAllocatedSharedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | done => simp [edgeBody, observed, Outcome.state, advance]
  | failed => simp [edgeBody, observed, Outcome.state, advance]

private theorem body_reads_fields {final : Memos}
    {actual : SourceCurrentAllocatedSharedPartialGraph.EdgeBody budget request before result after}
    (reads : SourceCurrentAllocatedSharedPartialEndpointReads.EdgeBodyReads formulas solver actual memos final)
    (initial : Context formulas solver inventory before memos)
    (typedState : SharedReady lib (initialShared before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (ready : EdgeReady before request) (closed : ClosedValues request.value.children)
    (classified : TypeRow lib request.value ∨
      SourceSynthesisHereditaryProgramFields.EdgeFields (Origin lib) literal request.value) :
    EdgeFields lib literal request result ∧ SharedReady lib (initialShared after.checked after.merge) ∧
      Extension before.checked.native.machine after.checked.native.machine ∧
      ClosedValues result.children ∧ GuardHeap (Origin lib) after.checked.native.machine.heap := by
  have physical : SharedReady lib (initialShared after.checked after.merge) ∧
      Extension before.checked.native.machine after.checked.native.machine ∧
      ClosedValues result.children ∧ GuardHeap (Origin lib) after.checked.native.machine.heap := by
    cases reads with
    | parent numeric =>
        rcases classified with typed | program
        · obtain ⟨next, extension, _resident, resultClosed, afterGuards, _typed, _coupled⟩ :=
            SourceSynthesisNativeTypeAnnotatedSharedParentWorker.receipt_fields lib formulas solver
              numeric initial typedState guards ready.1 ready.2 closed typed
          exact ⟨next, extension, resultClosed, afterGuards⟩
        · obtain ⟨next, extension, _resident, resultClosed, afterGuards, _fields⟩ :=
            SourceSynthesisNativeTypeHereditarySharedParentWorker.receipt_fields lib literal formulas solver
              numeric initial typedState guards ready.1 ready.2 closed program
          exact ⟨next, extension, resultClosed, afterGuards⟩
  refine ⟨⟨?_, fun _ => physical.2.2.1⟩, physical⟩
  constructor
  · intro typed
    cases reads with
    | parent numeric =>
        obtain ⟨_, _, _, _, _, outputTyped, _⟩ :=
          SourceSynthesisNativeTypeAnnotatedSharedParentWorker.receipt_fields lib formulas solver
            numeric initial typedState guards ready.1 ready.2 closed typed
        exact outputTyped
  · intro program
    cases reads with
    | parent numeric =>
        obtain ⟨_, _, _, _, _, outputFields⟩ :=
          SourceSynthesisNativeTypeHereditarySharedParentWorker.receipt_fields lib literal formulas solver
            numeric initial typedState guards ready.1 ready.2 closed program
        exact outputFields

/-- Every actual shared Parent outcome retains both complete outer histories. -/
theorem edgeBody_history (history : History lib literal before) :
    History lib literal (edgeBody fuel g s r e p h m c n budget request before).state := by
  have tables := edgeBody_tables (fuel := fuel) (g := g) (s := s) (r := r) (e := e)
    (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) (request := request) (before := before) rfl
  exact ⟨by rw [tables.1]; exact history.nodes, by rw [tables.2]; exact history.edges⟩
end Core

section Resources
variable {bits : Nat} {before after : Caller (bits + 2)}
variable {alphabet : List Guard} {entry : Profile}
variable (initial : Context formulas solver inventory before memos)
variable (frame : Frame formulas solver inventory before.checked)
variable (fits : Fits entry before.checked)
variable (known : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
variable (uniform : UniformReserved bits budget alphabet entry)
variable (typedState : SharedReady lib (initialShared before.checked before.merge))
variable (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
variable (ready : EdgeReady before request)
variable (closed : ClosedValues request.value.children)
variable (classified : TypeRow lib request.value ∨
  SourceSynthesisHereditaryProgramFields.EdgeFields (Origin lib) literal request.value)
include initial frame fits known uniform typedState guards ready closed classified

/-- Initial resources derive the body graph, reads and hereditary fields at the observed return. -/
theorem edgeBody_verified_fields
    (done : edgeBody fuel g s r e p h m c n budget request before = .done result after) :
    ∃ next final, ∃ graph : SourceCurrentAllocatedSharedPartialGraph.EdgeBody budget request before result after,
      SourceCurrentAllocatedSharedPartialEndpointReads.EdgeBodyReads formulas solver graph memos final ∧
      SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result after final ∧
      Post formulas solver next before after final ∧ Frame formulas solver next after.checked ∧
      Fits (outputProfile budget alphabet entry) after.checked ∧
      Carrier (fun guard => guard ∈ outputAlphabet budget alphabet entry) after.checked.native.machine.heap ∧
      InternedEdgeResidency.EdgeResident after.checked.native.machine.heap result ∧
      SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver request result ∧
      EdgeFields lib literal request result ∧ SharedReady lib (initialShared after.checked after.merge) ∧
      Extension before.checked.native.machine after.checked.native.machine ∧ ClosedValues result.children ∧
      GuardHeap (Origin lib) after.checked.native.machine.heap := by
  obtain ⟨next, final, receipt, numeric, carrier⟩ :=
    SourceCurrentSharedOuterEdgeGuardAlphabet.edge_body formulas solver inventory budget alphabet request before memos
      initial frame entry fits known ready.1 ready.2 uniform done
  obtain ⟨fields, nextReady, extension, resultClosed, afterGuards⟩ :=
    body_reads_fields receipt.reads initial typedState guards ready closed classified
  exact ⟨next, final, receipt.actual, receipt.reads, receipt.semantic, receipt.post, receipt.frame,
    numeric, carrier, receipt.semantic.resident, receipt.semantic.language,
    fields, nextReady, extension, resultClosed, afterGuards⟩

/-- The actual shared Parent return supplies the captured owner's publication implications. -/
theorem edgeBody_fields
    (done : edgeBody fuel g s r e p h m c n budget request before = .done result after) :
    EdgeFields lib literal request result := by
  obtain ⟨next, final, receipt, _numeric, _carrier⟩ :=
    SourceCurrentSharedOuterEdgeGuardAlphabet.edge_body formulas solver inventory budget alphabet request before memos
      initial frame entry fits known ready.1 ready.2 uniform done
  exact (body_reads_fields receipt.reads initial typedState guards ready closed classified).1

/-- Actual warm and cold calls retain both histories and their classified physical posts. -/
theorem edgeCall_fields (history : History lib literal before) :
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
        SourceCurrentAllocatedSharedPartialCallSteps.edge_start formulas solver initial ready.1 ready.2 started
      have ownerReady : EdgeReady running owner := ⟨ownerFacts.inherited, ownerFacts.input⟩
      have components := beginEdge_components request before
      rw [started] at components
      dsimp only at components
      obtain ⟨checkedSame, mergeSame, _fourth, _nodes⟩ := components
      have runningTyped : SharedReady lib (initialShared running.checked running.merge) := by
        simpa only [checkedSame, mergeSame] using typedState
      have runningGuards : GuardHeap (Origin lib) running.checked.native.machine.heap := by
        simpa only [checkedSame] using guards
      have runningFrame : Frame formulas solver inventory running.checked := by
        simpa only [checkedSame] using frame
      have runningFits : Fits entry running.checked := by simpa only [checkedSame] using fits
      have runningKnown : Carrier (fun guard => guard ∈ alphabet) running.checked.native.machine.heap := by
        simpa only [checkedSame] using known
      have ownerBefore : EdgeReady before owner := by simpa only [EdgeReady, checkedSame] using ownerReady
      have ownerSame : owner = request :=
        SourceSynthesisProgramMemoRoles.edge_same_key good ownerBefore ready sameKey
      have ownerClosed : ClosedValues owner.value.children := by simpa only [ownerSame] using closed
      have ownerClassified : TypeRow lib owner.value ∨
          SourceSynthesisHereditaryProgramFields.EdgeFields (Origin lib) literal owner.value := by
        simpa only [ownerSame] using classified
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
          obtain ⟨next, final, graph, reads, semantic, post, _frame, _fits, _known,
              _resident, _law, published, nextReady, extension, resultClosed, afterGuards⟩ :=
            edgeBody_verified_fields (entry := entry) runningContext runningFrame runningFits runningKnown uniform
              runningTyped runningGuards ownerReady ownerClosed ownerClassified body
          have finished := SourceSynthesisHereditaryClosedMemo.finishEdge middleHistory foundMiddle published
          refine ⟨?_, ?_⟩
          · simpa only [edgeCall, started, body, Outcome.bind, Outcome.state] using finished
          · intro output final actual
            simp only [edgeCall, started, body, Outcome.bind] at actual
            cases actual
            have candidateFields : EdgeFields lib literal request value := by simpa only [ownerSame] using published
            refine ⟨candidateFields, ?_, ?_, resultClosed, ?_⟩
            · simpa only [finishEdge] using nextReady
            · simpa only [finishEdge, checkedSame] using extension
            · simpa only [finishEdge] using afterGuards

/-- Initial resources derive the same successful call receipt and both complete histories. -/
theorem edgeCall_verified_fields (history : History lib literal before)
    (done : edgeCall fuel g s r e p h m c n budget request before = .done result after) :
    ∃ next final, ∃ graph : SourceCurrentAllocatedSharedPartialGraph.EdgeCall budget request before result after,
      SourceCurrentAllocatedSharedPartialEndpointReads.EdgeCallReads formulas solver graph memos final ∧
      SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result after final ∧
      Post formulas solver next before after final ∧ Frame formulas solver next after.checked ∧
      Fits (outputProfile budget alphabet entry) after.checked ∧
      Carrier (fun guard => guard ∈ outputAlphabet budget alphabet entry) after.checked.native.machine.heap ∧
      InternedEdgeResidency.EdgeResident after.checked.native.machine.heap result ∧
      SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver request result ∧
      History lib literal after ∧ EdgeFields lib literal request result ∧
      SharedReady lib (initialShared after.checked after.merge) ∧
      Extension before.checked.native.machine after.checked.native.machine ∧ ClosedValues result.children ∧
      GuardHeap (Origin lib) after.checked.native.machine.heap := by
  obtain ⟨next, final, receipt, numeric, carrier⟩ :=
    SourceCurrentSharedOuterEdgeGuardAlphabet.edge_call formulas solver inventory budget alphabet request before memos
      initial frame entry fits known ready.1 ready.2 uniform done
  have retained := edgeCall_fields (fuel := fuel) (g := g) (s := s) (r := r) (e := e)
    (p := p) (h := h) (m := m) (c := c) (n := n)
    initial frame fits known uniform typedState guards ready closed classified history
  have afterHistory : History lib literal after := by simpa only [done, Outcome.state] using retained.1
  obtain ⟨fields, nextReady, extension, resultClosed, afterGuards⟩ := retained.2 result after done
  exact ⟨next, final, receipt.actual, receipt.reads, receipt.semantic, receipt.post, receipt.frame,
    numeric, carrier, receipt.semantic.resident, receipt.semantic.language,
    afterHistory, fields, nextReady, extension, resultClosed, afterGuards⟩
end Resources
end MicroCFTA.SourceSynthesisHereditarySharedOuterEdgeWorker
