import MicroCFTA.SourceCurrentAllocatedPartialWorkerLeafActual
import MicroCFTA.SourceCurrentAllocatedPartialWorkerStability

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerLeafActual.edgeBody_verified
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerLeafActual.edgeBody_verified
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerLeafActual.node_ready
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerLeafActual.node_ready
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerLeafActual.edge_ready
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerLeafActual.edge_ready

namespace LeafActualChecks
open MicroCFTA
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw EdgeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

theorem body_same_complete_caller
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {fuel g s r e p h m c n budget : Nat}
    {request : EdgeRequest} {before after : Caller width} {result : Edge} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (ranges : SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before)
    (done : SourceCurrentAllocatedPartialWorker.edgeBody fuel g s r e p h m c n budget request before = .done result after) :
    ∃ next final,
      Post formulas solver next before after final ∧ Resident after.checked.native.machine.heap result ∧
      InternedFreshOrdinaryProbeHeap.Heap after.checked.native.machine.heap ∧ EdgeLaw formulas solver request result ∧
      after.nodeResults = before.nodeResults ∧ after.edgeResults = before.edgeResults := by
  obtain ⟨next, final, actual, _, receipt, post⟩ :=
    SourceCurrentAllocatedPartialWorkerLeafActual.edgeBody_verified formulas solver initial inherited resident ranges done
  have edges : after.edgeResults = before.edgeResults := by cases actual; rfl
  exact ⟨next, final, post, receipt.resident, post.context.probes, receipt.language, receipt.nodes, edges⟩

theorem ready_node_all_bounds
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {budget handle : Nat} {request : NodeRequest}
    {before after : Caller width} {result : Node} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (started : beginNode request before = (handle, .ready result, after))
    (fuel g s r e p h m c n : Nat) :
    ∃ actual : SourceCurrentAllocatedPartialGraph.NodeCall budget request before result after,
      SourceCurrentAllocatedPartialSourceReads.NodeCallReads formulas solver actual memos memos ∧
      SourceCurrentAllocatedPartialWorker.nodeCall fuel g s r e p h m c n budget request before = .done result after ∧
      Post formulas solver inventory before after memos ∧ NodeLaw formulas solver request result := by
  obtain ⟨actual, reads, zero, post, _, law⟩ :=
    SourceCurrentAllocatedPartialWorkerLeafActual.node_ready formulas solver initial inherited available started
  have done := SourceCurrentAllocatedPartialWorkerStability.nodeCall_done_stable zero
    (Nat.zero_le fuel) (Nat.zero_le g) (Nat.zero_le s) (Nat.zero_le r) (Nat.zero_le e)
    (Nat.zero_le p) (Nat.zero_le h) (Nat.zero_le m) (Nat.zero_le c) (Nat.zero_le n)
  exact ⟨actual, reads, done, post, law⟩

theorem ready_edge_all_bounds
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {budget handle : Nat} {request : EdgeRequest}
    {before after : Caller width} {result : Edge} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (started : beginEdge request before = (handle, .ready result, after))
    (fuel g s r e p h m c n : Nat) :
    ∃ actual : SourceCurrentAllocatedPartialGraph.EdgeCall budget request before result after,
      SourceCurrentAllocatedPartialSourceReads.EdgeCallReads formulas solver actual memos memos ∧
      SourceCurrentAllocatedPartialWorker.edgeCall fuel g s r e p h m c n budget request before = .done result after ∧
      Post formulas solver inventory before after memos ∧ EdgeLaw formulas solver request result := by
  obtain ⟨actual, reads, zero, post, _, law⟩ :=
    SourceCurrentAllocatedPartialWorkerLeafActual.edge_ready formulas solver initial inherited resident started
  have done := SourceCurrentAllocatedPartialWorkerStability.edgeCall_done_stable zero
    (Nat.zero_le fuel) (Nat.zero_le g) (Nat.zero_le s) (Nat.zero_le r) (Nat.zero_le e)
    (Nat.zero_le p) (Nat.zero_le h) (Nat.zero_le m) (Nat.zero_le c) (Nat.zero_le n)
  exact ⟨actual, reads, done, post, law⟩

theorem actual_owner_body_finish
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {fuel g s r e p h m c n budget handle : Nat}
    {request owner : EdgeRequest} {before running middle : Caller width} {result : Edge} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (started : beginEdge request before = (handle, .evaluate owner, running))
    (ranges : SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget owner running)
    (bodyDone : SourceCurrentAllocatedPartialWorker.edgeBody fuel g s r e p h m c n budget owner running = .done result middle) :
    ∃ next final,
      ∃ actual : SourceCurrentAllocatedPartialGraph.EdgeCall budget request before result (finishEdge handle result middle),
        SourceCurrentAllocatedPartialSourceReads.EdgeCallReads formulas solver actual memos final ∧
        SourceCurrentAllocatedPartialWorker.edgeCall fuel g s r e p h m c n budget request before =
          .done result (finishEdge handle result middle) ∧
        Post formulas solver next before (finishEdge handle result middle) final ∧
        Resident (finishEdge handle result middle).checked.native.machine.heap result ∧ EdgeLaw formulas solver request result := by
  obtain ⟨current, ownerGood, _, _⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start
    formulas solver initial inherited resident started
  obtain ⟨next, final, body, reads, receipt, post⟩ :=
    SourceCurrentAllocatedPartialWorkerLeafActual.edgeBody_verified formulas solver current ownerGood.inherited ownerGood.input ranges bodyDone
  obtain ⟨finished, available, law⟩ := SourceCurrentAllocatedPartialCallSteps.edge_finish
    formulas solver initial inherited resident started body post receipt.resident receipt.language
  exact ⟨next, final, .evaluate started body, .evaluate (started := started) reads,
    SourceCurrentAllocatedPartialWorker.edgeCall_body_done fuel g s r e p h m c n budget request owner
      before running middle handle result started bodyDone,
    finished, available, law⟩

end LeafActualChecks

#print axioms LeafActualChecks.body_same_complete_caller
#check @LeafActualChecks.body_same_complete_caller
#print axioms LeafActualChecks.ready_node_all_bounds
#check @LeafActualChecks.ready_node_all_bounds
#print axioms LeafActualChecks.ready_edge_all_bounds
#check @LeafActualChecks.ready_edge_all_bounds
#print axioms LeafActualChecks.actual_owner_body_finish
#check @LeafActualChecks.actual_owner_body_finish
