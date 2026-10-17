import MicroCFTA.SourceCurrentAllocatedNativeWidthStep
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.SourceEqualityRequiredSemanticCache

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.WidthStepIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativeWidthStep
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open InternedNestedConstruction (Syntax Outcome)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Control" => SourceEqualityNativeDemand.Control
local notation "Stored" => InternedValueMassHeap.Stored
local notation "ceiling" => SourceCurrentAllocatedRecursiveMassTrace.ceiling
local notation "Fields" => SourceCurrentAllocatedNativeFieldClosure.Fields
local notation "Physical" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
variable [DecidableEq (EdgeKey Symbol Guard)]

private def expression : Syntax Symbol Guard := .binder false (.var 0)
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def original : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def before : Checked 8 := ⟨initial 8 machine, SourceEqualityConstraintMemoAllocation.empty⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, original, original⟩
private def running : Checked 8 := {before with native := (demandNode 0 (lookupNode 8 request before.native).2).2}
private def finished : Checked 8 := {running with native := finishNode 0 original running.native}
private def bound := InternedValueMassHeap.initialBound heap
private def post (state : Machine Symbol Guard) (value : Value Symbol Guard) := Available state.heap value

private theorem constructed : built = .done original heap := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, original, heap, done, Outcome.state]

private theorem initial_good : Good before := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression original heap constructed
  have noEdges : SourceEqualityAnnotationHeap.Heap (fun _ : Guard => False) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun _ : Guard => False) expression
      (by simp [expression, SourceEqualityAnnotationConstruction.Allowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built, heap] using checked
  exact ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid machine
    ⟨semantic.ready.semantic.1.normal.facts, Cache.empty_valid⟩,
    semantic.ready, SourceEqualityConstraintMemoAllocation.empty_valid,
    fun key edge found => (noEdges key edge found).elim⟩

private theorem available : Available heap original :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result original heap constructed

private theorem initial_stored : Stored bound heap := InternedValueMassHeap.initial heap initial_good.native.machine.1
private theorem ready : NodeReady machine request := ⟨empty_domain machine, available, available⟩
private theorem safe : SourceRecursiveIntersectionMemo.KeySafe 8 request.domain request.left request.right := by
  unfold SourceRecursiveIntersectionMemo.KeySafe
  refine ⟨by cbv, by cbv, .mu 0, .mu 0, ?_, ?_, ?_, ?_⟩ <;> cbv

variable [DecidableEq Symbol]

private theorem first_step : SourceEqualityNativeDemand.step (.code (.node request .pure)) before =
    .yielded (.code (.finishNode 0 original (.pure original))) running := by cbv
private theorem finish_step : SourceEqualityNativeDemand.step (.code (.finishNode 0 original (.pure original))) running =
    .yielded (.code (.pure original)) finished := rfl
private theorem warm_step : SourceEqualityNativeDemand.step (.code (.node request .pure)) finished =
    .yielded (.code (.pure original)) finished := by cbv

/-- An actual source-built Mu publishes its owner, retains the protectedCode width certificate, finishes, and reuses the exact warm result. -/
theorem cold_owner_then_warm :
    built = .done original heap ∧
    SourceEqualityNativeDemand.step (.code (.node request .pure)) before =
      .yielded (.code (.finishNode 0 original (.pure original))) running ∧
    running.native.nodes.cells 0 = some ⟨request, .evaluating⟩ ∧
    ControlAt (.code (.finishNode 0 original (.pure original))) running (ceiling bound) post ∧
    SourceEqualityNativeDemand.step (.code (.finishNode 0 original (.pure original))) running =
      .yielded (.code (.pure original)) finished ∧
    finished.native.nodes.cells 0 = some ⟨request, .returned original⟩ ∧
    SourceEqualityNativeDemand.step (.code (.node request .pure)) finished =
      .yielded (.code (.pure original)) finished ∧
    ControlAt (.code (.pure original)) finished (ceiling (ceiling (ceiling bound))) post ∧
    Good finished ∧ Stored (ceiling (ceiling bound)) finished.native.machine.heap := by
  have physical : Physical (.code (.node request .pure)) before := ⟨ready, fun _ _ => safe⟩
  have fields : Fields (.code (.node request .pure)) before := fun _ => trivial
  have certificate : ControlAt (.code (.node request .pure)) before bound post :=
    SourceRecursiveIntersectionCodeMass.request_node _ _ _ machine bound ready
  have protectedCode := yielded_at _ _ before running bound post initial_good physical fields initial_stored certificate first_step
  have effects := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants _ before initial_good physical fields
  have goodRunning : Good running := by simpa only [first_step, SourceEqualityNativeDemand.Outcome.state] using effects.1
  have runningStored : Stored (ceiling bound) running.native.machine.heap := by
    have own := SourceCurrentAllocatedRecursiveMassTrace.step_bound _ before initial_good physical initial_stored
      (inputs _ before bound certificate)
    simpa only [first_step, SourceEqualityNativeDemand.Outcome.state] using own.1
  have captured : running.native.nodes.cells 0 = some ⟨request, .evaluating⟩ := by cbv
  have sameMachine : running.native.machine = machine := by cbv
  have finishPhysical : Physical (.code (.finishNode 0 original (.pure original))) running :=
    ⟨request, captured, by rw [sameMachine]; exact available⟩
  have finishFields : Fields (.code (.finishNode 0 original (.pure original))) running := trivial
  have completed := yielded_at _ _ running finished (ceiling bound) post goodRunning finishPhysical finishFields
    runningStored protectedCode finish_step
  have finishEffects := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants _ running goodRunning finishPhysical finishFields
  have goodFinished : Good finished := by simpa only [finish_step, SourceEqualityNativeDemand.Outcome.state] using finishEffects.1
  have finishedStored : Stored (ceiling (ceiling bound)) finished.native.machine.heap := by
    have own := SourceCurrentAllocatedRecursiveMassTrace.step_bound _ running goodRunning finishPhysical runningStored
      (inputs _ running (ceiling bound) protectedCode)
    simpa only [finish_step, SourceEqualityNativeDemand.Outcome.state] using own.1
  have finishedMachine : finished.native.machine = machine := by cbv
  have finishedReady : NodeReady finished.native.machine request := by rw [finishedMachine]; exact ready
  have warmCertificate : ControlAt (.code (.node request .pure)) finished (ceiling (ceiling bound)) post :=
    SourceRecursiveIntersectionCodeMass.request_node _ _ _ _ _ finishedReady
  have warmPhysical : Physical (.code (.node request .pure)) finished := ⟨finishedReady, fun _ _ => safe⟩
  have warmFields : Fields (.code (.node request .pure)) finished := fun _ => trivial
  have reused := yielded_at _ _ finished finished (ceiling (ceiling bound)) post goodFinished warmPhysical warmFields
    finishedStored warmCertificate warm_step
  exact ⟨constructed, first_step, captured, protectedCode, finish_step, by cbv, warm_step, reused, goodFinished, finishedStored⟩

/-- A real constructor prefix advances its bound before the emitted node body, without a future width premise. -/
theorem work_then_node :
    ∃ row after,
      SourceEqualityNativeDemand.step (.code (.work (makeEdge (("mass", FullSyntax.Formula.tru))
        SourceEqualityConstraintConstructors.top [original]) .pure)) before = .yielded (.code (.pure row)) after ∧
      Stored (ceiling bound) after.native.machine.heap ∧
      InternedValueMass.edge row ≤ ceiling bound := by
  let job := makeEdge (("mass", FullSyntax.Formula.tru)) SourceEqualityConstraintConstructors.top [original]
  let actual := run job heap
  let after : Checked 8 := {before with native := advance before.native {machine with heap := actual.2}}
  have one : SourceEqualityNativeDemand.step (.code (.work job .pure)) before = .yielded (.code (.pure actual.1)) after := rfl
  have width : 1 ≤ bound * bound := by
    have positive := initial_stored.positive
    have square := Nat.mul_le_mul positive positive
    simpa only [Nat.one_mul] using square
  have jobInputs : SourceRecursiveIntersectionWorkMass.Inputs (bound * bound) heap job :=
    .edge _ _ [original] (by intro value member; cases List.mem_singleton.mp member; exact available) width
  have actualMass := SourceRecursiveIntersectionWorkMass.edge _ _ [original] heap initial_stored
    (by intro value member; cases List.mem_singleton.mp member; exact InternedValueMassHeap.available heap initial_stored original available)
  have chosen : InternedFreshOrdinaryResultMass.inflate 1 bound ≤ ceiling bound := by
    have larger := SourceRecursiveIntersectionWorkMass.inflate_width width bound
    exact Nat.le_trans larger (Nat.le_max_left _ _)
  exact ⟨actual.1, after, one, (SourceRecursiveIntersectionWorkMass.run_bound initial_stored jobInputs).1.mono (Nat.le_max_left _ _),
    Nat.le_trans actualMass.2.1 chosen⟩

#print axioms cold_owner_then_warm
#check @cold_owner_then_warm
#print axioms work_then_node
#check @work_then_node
end MicroCFTA.WidthStepIntegration
