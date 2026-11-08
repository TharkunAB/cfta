import MicroCFTA.SourceSynthesisProgramMemoRoles
import MicroCFTA.SourceSynthesisParentProgramRoles
import MicroCFTA.SourceCurrentAllocatedPartialCallSteps

/-!
# Strict Program roles through actual outer edge calls

Actual Parent returns supply strict row roles. Warm edge results use their
captured requests and complete physical keys. Both result tables retain
their conditional role history on successful and failed edge outcomes.
The incoming history and caller facts are local induction hypotheses.
-/
namespace MicroCFTA.SourceSynthesisOuterEdgeProgramRoles
open InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisProgramBuildRolesGeneric (ProgramEdge)
open SourceSynthesisProgramMemoRoles (History)
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentOuterPrefixInvariants (Good EdgeReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width : Nat} {literal : String → Symbol}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest}
variable {before after : Caller width} {result : Edge}

private theorem edgeBody_tables {output : Outcome Edge width}
    (actual : edgeBody fuel g s r e p h m c n budget request before = output) :
    output.state.nodeResults = before.nodeResults ∧ output.state.edgeResults = before.edgeResults := by
  rw [← actual]
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | done value checked fourth memo =>
      simp [edgeBody, observed, Outcome.state, advance]
  | failed fault checked fourth memo =>
      simp [edgeBody, observed, Outcome.state, advance]

/-- Every Parent outcome retains both outer role histories. -/
theorem edgeBody_history (history : History literal before) :
    History literal (edgeBody fuel g s r e p h m c n budget request before).state := by
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | done value checked fourth memo =>
      simpa only [edgeBody, observed, Outcome.state] using
        SourceSynthesisProgramMemoRoles.advance history checked fourth memo
  | failed fault checked fourth memo =>
      simpa only [edgeBody, observed, Outcome.state] using
        SourceSynthesisProgramMemoRoles.advance history checked fourth memo

/-- The actual successful body derives its strict role from the original caller inputs. -/
theorem edgeBody_roles
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory} {memos : Memos}
    (actual : edgeBody fuel g s r e p h m c n budget request before = .done result after)
    (initial : Context formulas solver inventory before memos)
    (ready : EdgeReady before request) (role : ProgramEdge literal request.value) :
    ProgramEdge literal result := by
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | failed => simp only [edgeBody, observed] at actual; cases actual
  | done value checked fourth memo =>
      simp only [edgeBody, observed] at actual
      cases actual
      have good := SourceCurrentNativeOperationHeap.Good.of_native
        (SourceCurrentNativeOperationInvariants.Good.of_checked initial.ready.good)
        initial.ready.semantic initial.ready.costs
      exact SourceSynthesisParentProgramRoles.edge_roles formulas solver observed initial role
        (fun _ => ⟨good.fields request.value.entry.key request.value ready.2, ready.1,
          good.heap.semantic.1.normal.facts.cached.edges request.value.entry.key request.value ready.2⟩)

/-- Actual edge calls retain history on every outcome and strict roles on every return. -/
theorem edgeCall_program
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos) (good : Good before)
    (ready : EdgeReady before request) (history : History literal before) :
    History literal (edgeCall fuel g s r e p h m c n budget request before).state ∧
      ∀ output final, edgeCall fuel g s r e p h m c n budget request before = .done output final →
        ProgramEdge literal request.value → ProgramEdge literal output := by
  rcases started : beginEdge request before with ⟨handle, action, running⟩
  have runningHistory := SourceSynthesisProgramMemoRoles.beginEdge history request
  rw [started] at runningHistory
  dsimp only at runningHistory
  cases action with
  | busy | absent =>
      refine ⟨?_, ?_⟩
      · simpa only [edgeCall, started, Outcome.state] using runningHistory
      · intro output final actual role
        simp only [edgeCall, started] at actual
        cases actual
  | ready value =>
      refine ⟨?_, ?_⟩
      · simpa only [edgeCall, started, Outcome.state] using runningHistory
      · intro output final actual role
        simp only [edgeCall, started] at actual
        cases actual
        exact (SourceSynthesisProgramMemoRoles.edge_ready history good ready started role).2
  | evaluate owner =>
      obtain ⟨runningContext, ownerFacts, sameKey, found⟩ :=
        SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver initial ready.1 ready.2 started
      have ownerReady : EdgeReady running owner := ⟨ownerFacts.inherited, ownerFacts.input⟩
      have checkedSame := (beginEdge_components request before).1
      rw [started] at checkedSame
      dsimp only at checkedSame
      have ownerBefore : EdgeReady before owner := by
        simpa only [EdgeReady, checkedSame] using ownerReady
      have ownerSame : owner = request :=
        SourceSynthesisProgramMemoRoles.edge_same_key good ownerBefore ready sameKey
      have bodyHistory := edgeBody_history (fuel := fuel) (g := g) (s := s) (r := r) (e := e)
        (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) (request := owner) runningHistory
      cases body : edgeBody fuel g s r e p h m c n budget owner running with
      | failed fault middle =>
          refine ⟨?_, ?_⟩
          · simpa only [edgeCall, started, body, Outcome.bind, Outcome.state] using bodyHistory
          · intro output final actual role
            simp only [edgeCall, started, body, Outcome.bind] at actual
            cases actual
      | done value middle =>
          have middleHistory : History literal middle := by
            simpa only [body, Outcome.state] using bodyHistory
          have foundMiddle : middle.edgeResults.cells handle = some ⟨owner, .evaluating⟩ := by
            have tables : middle.edgeResults = running.edgeResults := (edgeBody_tables body).2
            rw [tables]
            exact found
          have published : ProgramEdge literal owner.value → ProgramEdge literal value :=
            fun role => edgeBody_roles formulas solver body runningContext ownerReady role
          have finished := SourceSynthesisProgramMemoRoles.finishEdge middleHistory foundMiddle published
          refine ⟨?_, ?_⟩
          · simpa only [edgeCall, started, body, Outcome.bind, Outcome.state] using finished
          · intro output final actual role
            simp only [edgeCall, started, body, Outcome.bind] at actual
            cases actual
            apply published
            simpa only [ownerSame] using role

end MicroCFTA.SourceSynthesisOuterEdgeProgramRoles
