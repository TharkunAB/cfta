import MicroCFTA.SourceCurrentAllocatedRecursiveMassMonotone
import MicroCFTA.SourceCurrentAllocatedNativeWidthTrace
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

namespace MicroCFTA.MassMonotoneIntegration
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
local notation "massAfter" => SourceCurrentAllocatedRecursiveMassTrace.massAfter
local notation "credit" => SourceCurrentAllocatedRecursiveMassTrace.credit
open SourceCurrentAllocatedRecursiveMassMonotone
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
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

/-- A checked prefix uses a larger initial numeric budget without another width plan or intermediate heap bound. -/
theorem budgeted_prefix {width count budget initial chosen : Nat} {A : Type}
    {control next : Control A} {start final : Checked width}
    (actual : Trace count control start next final) (good : Good start) (fields : Fields control start)
    (stored : Stored initial start.native.machine.heap)
    (certificate : ControlAt control start initial resultPost)
    (counts : count ≤ budget) (bounds : initial ≤ chosen) :
    Good final ∧ Stored (massAfter budget chosen) final.native.machine.heap ∧
    ControlAt next final (massAfter budget chosen) resultPost ∧
    final.native.machine.heap.nodes.next ≤ start.native.machine.heap.nodes.next + credit budget chosen ∧
    final.native.machine.heap.edges.next ≤ start.native.machine.heap.edges.next + credit budget chosen ∧
    final.native.machine.domains.next ≤ start.native.machine.domains.next + budget := by
  obtain ⟨_inputs, lastAt, lastGood, _fields, lastStored, nodes, edges, domains⟩ :=
    SourceCurrentAllocatedNativeWidthTrace.prefix_bound actual good fields stored certificate
  have mass := massAfter_mono counts bounds
  have paid := credit_mono counts bounds
  exact ⟨lastGood, lastStored.mono mass, ControlAt.mono next final lastAt mass,
    Nat.le_trans nodes (Nat.add_le_add_left paid _),
    Nat.le_trans edges (Nat.add_le_add_left paid _),
    Nat.le_trans domains (Nat.add_le_add_left counts _)⟩

/-- A source-built Mu constructs cold and warm executions, then uses strictly larger count and mass budgets at both exact returns. -/
theorem constructed_cold_warm_budget :
    built = .done original heap ∧
    SourceEqualityNativeDemand.execute 3 (.code (requestNode request.domain request.left request.right)) before =
      .done original finished ∧
    SourceEqualityNativeDemand.execute 2 (.code (requestNode request.domain request.left request.right)) finished =
      .done original finished ∧
    finished.native.nodes.cells 0 = some ⟨request, .returned original⟩ ∧
    Stored (massAfter 4 (bound + 3)) finished.native.machine.heap ∧
    InternedValueMass.value original ≤ massAfter 4 (bound + 3) ∧
    finished.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + credit 4 (bound + 3) ∧
    finished.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + credit 4 (bound + 3) ∧
    finished.native.machine.domains.next ≤ before.native.machine.domains.next + 4 ∧
    2 < 4 ∧ bound < bound + 3 := by
  have firstPhysical : Physical (.code (.node request .pure)) before := ⟨ready, fun _ _ => safe⟩
  have captured : running.native.nodes.cells 0 = some ⟨request, .evaluating⟩ := by cbv
  have sameMachine : running.native.machine = machine := by cbv
  have finishPhysical : Physical (.code (.finishNode 0 original (.pure original))) running :=
    ⟨request, captured, by rw [sameMachine]; exact available⟩
  have actual : Trace 2 (.code (requestNode request.domain request.left request.right)) before
      (.code (.pure original)) finished :=
    .cons _ _ _ _ _ _ _ firstPhysical first_step
      (.cons _ _ _ _ _ _ _ finishPhysical finish_step (.refl _ _))
  have facts := SourceCurrentAllocatedNativeWidthTrace.node_prefix request actual initial_good ready
  obtain ⟨done, _stored, resultMass, nodes, edges, domains⟩ :=
    SourceCurrentAllocatedNativeWidthTrace.node_return request original actual initial_good ready
  have mass : massAfter 2 bound ≤ massAfter 4 (bound + 3) := massAfter_mono (by decide) (by omega)
  have paid : credit 2 bound ≤ credit 4 (bound + 3) := credit_mono (by decide) (by omega)
  have warmReady : NodeReady finished.native.machine request := by
    have same : finished.native.machine = machine := by cbv
    rw [same]
    exact ready
  have warmPhysical : Physical (.code (.node request .pure)) finished := ⟨warmReady, fun _ _ => safe⟩
  have warmTrace : Trace 1 (.code (requestNode request.domain request.left request.right)) finished
      (.code (.pure original)) finished := .cons _ _ _ _ _ _ _ warmPhysical warm_step (.refl _ _)
  have warm := SourceCurrentAllocatedNativeWidthTrace.node_return request original warmTrace facts.2.2.1 warmReady
  exact ⟨constructed, done, warm.1, by cbv, facts.2.2.2.2.1.mono mass,
    Nat.le_trans resultMass mass,
    Nat.le_trans nodes (Nat.add_le_add_left paid _), Nat.le_trans edges (Nat.add_le_add_left paid _),
    Nat.le_trans domains (Nat.add_le_add_left (by decide : 2 ≤ 4) _), by decide, by omega⟩

#print axioms budgeted_prefix
#check @budgeted_prefix
#print axioms constructed_cold_warm_budget
#check @constructed_cold_warm_budget
end MicroCFTA.MassMonotoneIntegration
