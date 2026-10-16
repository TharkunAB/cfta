import MicroCFTA.SourceCurrentAllocatedPartialCallSteps
import MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges

namespace MicroCFTA.OuterProgressBoundaryProbe
open InternedConstructorTemplates InternedProbeProvenance SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialInvariant
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

-- Actual publication retains Context. It does not make this owner's recursive demand complete.
theorem fresh_owner_boundary
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {before : Caller width} {memos : EndpointMemoGateTrace.Memos}
    (initial : Context formulas solver inventory before memos) (request : NodeRequest)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (missing : before.nodeResults.table request.key = none) :
    ∃ running,
      beginNode request before = (before.nodeResults.next, .evaluate request, running) ∧
      Context formulas solver inventory running memos ∧
      SourceEqualityConstraintAllocation.Ready running.checked.operations.constraints request.inherited ∧
      Available running.checked.native.machine.heap request.value ∧
      running.nodeResults.table request.key = some before.nodeResults.next ∧
      running.nodeResults.cells before.nodeResults.next = some ⟨request, .evaluating⟩ ∧
      ∀ fuel g s r e p h m c n budget,
        SourceCurrentAllocatedPartialWorkerRanges.nodeCall fuel g s r e p h m c n budget request running ∧
        SourceCurrentAllocatedPartialWorker.nodeCall fuel g s r e p h m c n budget request running =
          .failed (.nodeMemo before.nodeResults.next .busy) running := by
  let running : Caller width := { before with nodeResults := (FlatMemoThunk.setStatus before.nodeResults.next .evaluating
      (FlatMemoThunk.lookupOrInsert request.key request before.nodeResults).2) }
  have fresh := SourceCurrentAllocatedPartialMemoSound.beginNode_fresh request before missing
  have started : beginNode request before = (before.nodeResults.next, .evaluate request, running) := fresh.1
  have next := SourceCurrentAllocatedPartialCallSteps.node_start formulas solver initial inherited available started
  have published : running.nodeResults.table request.key = some before.nodeResults.next := by
    simp only [running, FlatMemoThunk.setStatus,
      (FlatMemoThunk.lookup_miss request.key request before.nodeResults missing).2.2]
    exact (FlatMemoThunk.lookup_miss request.key request before.nodeResults missing).2.1
  have busy := beginNode_busy request request running before.nodeResults.next published next.2.2.2
  refine ⟨running, started, next.1, next.2.1.inherited, next.2.1.input, published, next.2.2.2, ?_⟩
  intro fuel g s r e p h m c n budget
  exact ⟨by simp only [SourceCurrentAllocatedPartialWorkerRanges.nodeCall, busy],
    SourceCurrentAllocatedPartialWorker.nodeCall_busy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ busy⟩

#print axioms fresh_owner_boundary
#check fresh_owner_boundary
end MicroCFTA.OuterProgressBoundaryProbe
