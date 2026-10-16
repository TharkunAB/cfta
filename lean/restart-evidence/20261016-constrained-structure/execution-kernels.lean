import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryExecution

namespace FiniteOrdinaryExecutionKernels
open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryStored
open SourceCurrentAllocatedFiniteOrdinaryCode (NodeInputs EdgeInputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State

def emptyRequest : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, .empty, .empty⟩
def cold (machine : Machine Symbol Guard) (operations : Operations) : Checked 8 :=
  ⟨initial 8 machine, operations⟩
def chosen (machine : Machine Symbol Guard) : Native 8 Symbol Guard :=
  (lookupNode 8 emptyRequest (initial 8 machine)).2
def running (machine : Machine Symbol Guard) (operations : Operations) : Checked 8 :=
  ⟨(demandNode 0 (chosen machine)).2, operations⟩
def finished (machine : Machine Symbol Guard) (operations : Operations) : Checked 8 :=
  {running machine operations with native := finishNode 0 .empty (running machine operations).native}

private theorem empty_safe : SourceRecursiveIntersectionMemo.KeySafe 8 emptyRequest.domain emptyRequest.left emptyRequest.right := by
  exact ⟨by decide, by decide, .empty, .empty, rfl, rfl, trivial, trivial⟩

private theorem empty_ready (machine : Machine Symbol Guard) : NodeReady machine emptyRequest :=
  ⟨empty_domain machine, empty_available _, empty_available _⟩

private theorem empty_inputs : NodeInputs emptyRequest := ⟨rfl, .empty, .empty⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

theorem cold_empty_installs_its_actual_owner
    (machine : Machine Symbol Guard) (operations : Operations)
    (good : Good (cold machine operations)) (semantic : SemanticReady machine.heap) :
    Trace 2 (.code (requestNode emptyRequest.domain emptyRequest.left emptyRequest.right)) (cold machine operations)
      (.code (.pure (.empty : Node))) (finished machine operations) ∧
    Stored (finished machine operations).native ∧ SourceCurrentAllocatedFiniteOrdinaryDomain.Node (.empty : Node) ∧
    MergedOrdinaryHeight.height (.empty : Node) = 0 ∧
    (finished machine operations).native.nodes.cells 0 = some ⟨emptyRequest, .returned .empty⟩ ∧
    (finished machine operations).native.machine = machine ∧ (finished machine operations).operations = operations := by
  have first : step (.code (requestNode emptyRequest.domain emptyRequest.left emptyRequest.right)) (cold machine operations) =
      .yielded (.code (.finishNode 0 .empty (.pure .empty))) (running machine operations) := by rfl
  have owner : (running machine operations).native.nodes.cells 0 = some ⟨emptyRequest, .evaluating⟩ := by rfl
  have trace : Trace 2 (.code (requestNode emptyRequest.domain emptyRequest.left emptyRequest.right)) (cold machine operations)
      (.code (.pure (.empty : Node))) (finished machine operations) := by
    refine .cons _ _ _ _ _ _ 1 ⟨empty_ready machine, fun _ _ => empty_safe⟩ first ?_
    exact .cons _ _ _ _ _ _ 0 ⟨emptyRequest, owner, empty_available _⟩ rfl (.refl _ _)
  have result := SourceCurrentAllocatedFiniteOrdinaryExecution.node_trace emptyRequest _ _ 2 .empty trace
    good semantic (initial_stored 8 machine) empty_inputs
  exact ⟨trace, result.1, result.2.1, rfl, rfl, rfl, rfl⟩

theorem cold_then_warm_repeat_keeps_the_entire_checked_state
    (machine : Machine Symbol Guard) (operations : Operations)
    (good : Good (cold machine operations)) (semantic : SemanticReady machine.heap) :
    let after := finished machine operations
    Good after ∧ Stored after.native ∧
      Trace 1 (.code (requestNode emptyRequest.domain emptyRequest.left emptyRequest.right)) after
        (.code (.pure (.empty : Node))) after ∧
      execute 2 (.code (requestNode emptyRequest.domain emptyRequest.left emptyRequest.right)) after = .done .empty after ∧
      SourceCurrentAllocatedFiniteOrdinaryDomain.Node (.empty : Node) ∧ MergedOrdinaryHeight.height (.empty : Node) ≤ 0 := by
  obtain ⟨trace, stored, _domain, _height, _owner, _machine, _operations⟩ :=
    cold_empty_installs_its_actual_owner machine operations good semantic
  have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects trace good (fun _ => trivial)
  have warm : Trace 1 (.code (requestNode emptyRequest.domain emptyRequest.left emptyRequest.right))
      (finished machine operations) (.code (.pure (.empty : Node))) (finished machine operations) := by
    refine .cons _ _ _ _ _ _ 0 ⟨empty_ready machine, fun _ _ => empty_safe⟩ ?_ (.refl _ _)
    rfl
  have result := SourceCurrentAllocatedFiniteOrdinaryExecution.node_trace emptyRequest _ _ 1 .empty warm
    reached.1 semantic stored empty_inputs
  exact ⟨reached.1, result.1, warm, trace_done 1 _ _ _ _ warm.steps, result.2.1, result.2.2.1⟩

theorem actual_warm_edge_observation_constructs_its_checked_trace
    {width : Nat} (request : EdgeRequest Symbol Guard)
    (before : Checked width) (chosen after : Native width Symbol Guard) (handle : Nat) (result : Edge)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap) (stored : Stored before.native)
    (ready : EdgeReady before.native.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupEdge width request before.native = (handle, chosen))
    (demanded : demandEdge handle chosen = (.ready result, after)) (inputs : EdgeInputs request) :
    Trace 1 (.code (requestEdge request.domain request.left request.right)) before (.code (.pure result))
      ⟨after, before.operations⟩ ∧ Stored after ∧ SourceCurrentAllocatedFiniteOrdinaryDomain.Edge result ∧
      MergedOrdinaryHeight.edgeHeight result ≤ min (MergedOrdinaryHeight.edgeHeight request.left)
        (MergedOrdinaryHeight.edgeHeight request.right) := by
  have one : step (.code (requestEdge request.domain request.left request.right)) before =
      .yielded (.code (.pure result)) ⟨after, before.operations⟩ := by
    simp only [requestEdge, step, selected, demanded]
  have trace : Trace 1 (.code (requestEdge request.domain request.left request.right)) before (.code (.pure result))
      ⟨after, before.operations⟩ := .cons _ _ _ _ _ _ 0 ⟨ready, safe⟩ one (.refl _ _)
  have checked := SourceCurrentAllocatedFiniteOrdinaryExecution.edge_trace request _ _ 1 result trace good semantic stored inputs
  exact ⟨trace, checked.1, checked.2.1, Nat.le_min.mpr checked.2.2⟩

end FiniteOrdinaryExecutionKernels

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms FiniteOrdinaryExecutionKernels.cold_empty_installs_its_actual_owner
#check @FiniteOrdinaryExecutionKernels.cold_empty_installs_its_actual_owner
#print axioms FiniteOrdinaryExecutionKernels.cold_then_warm_repeat_keeps_the_entire_checked_state
#check @FiniteOrdinaryExecutionKernels.cold_then_warm_repeat_keeps_the_entire_checked_state
#print axioms FiniteOrdinaryExecutionKernels.actual_warm_edge_observation_constructs_its_checked_trace
#check @FiniteOrdinaryExecutionKernels.actual_warm_edge_observation_constructs_its_checked_trace
