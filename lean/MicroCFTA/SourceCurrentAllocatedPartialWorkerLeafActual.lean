import MicroCFTA.SourceCurrentAllocatedParentWorkerActual
import MicroCFTA.SourceCurrentAllocatedPartialWorker
import MicroCFTA.SourceCurrentAllocatedPartialCallSteps

/-!
# Actual literal outer parent leaves and ready hits

The successful parent observation identifies the entire returned caller.
Its resident original input derives the actual source body and strict reads.
Ready hits retain their exact demand state without invoking a body.
The inputs contain initial facts and reached checks, not a future body law.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialWorkerLeafActual
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

/-- A literal successful parent body derives strict source reads and its same complete caller return. -/
theorem edgeBody_verified
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {fuel g s r e p h m c n budget : Nat}
    {request : EdgeRequest} {before after : Caller width} {result : Edge} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (ranges : SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before)
    (done : SourceCurrentAllocatedPartialWorker.edgeBody fuel g s r e p h m c n budget request before = .done result after) :
    ∃ next final,
      ∃ actual : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result after,
        SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads formulas solver actual memos final ∧
        SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result after final ∧
        Post formulas solver next before after final := by
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget request.value.entry.key.symbol
      request.value.entry.key.constraint request.inherited request.value.children before.checked before.fourth before.merge with
  | done value checked fourth memo =>
      simp only [SourceCurrentAllocatedPartialWorker.edgeBody, observed] at done
      cases done
      exact SourceCurrentAllocatedParentWorkerActual.resident_verified formulas solver initial inherited resident ranges observed
  | failed =>
      simp only [SourceCurrentAllocatedPartialWorker.edgeBody, observed] at done
      cases done

/-- A ready node hit completes at zero bounds with its actual graph, reads, and candidate law. -/
theorem node_ready
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {budget handle : Nat} {request : NodeRequest}
    {before after : Caller width} {result : Node} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (started : beginNode request before = (handle, .ready result, after)) :
    ∃ actual : SourceCurrentAllocatedPartialGraph.NodeCall budget request before result after,
      SourceCurrentAllocatedPartialSourceReads.NodeCallReads formulas solver actual memos memos ∧
      SourceCurrentAllocatedPartialWorker.nodeCall 0 0 0 0 0 0 0 0 0 0 budget request before = .done result after ∧
      Post formulas solver inventory before after memos ∧
      Available after.checked.native.machine.heap result ∧ NodeLaw formulas solver request result := by
  obtain ⟨post, resident, law⟩ := SourceCurrentAllocatedPartialCallSteps.node_hit formulas solver initial inherited available started
  exact ⟨.hit started, .hit (started := started),
    SourceCurrentAllocatedPartialWorker.nodeCall_ready 0 0 0 0 0 0 0 0 0 0 budget request before after handle result started,
    post, resident, law⟩

/-- A ready edge hit skips every parent stage and retains its actual caller and candidate law. -/
theorem edge_ready
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {budget handle : Nat} {request : EdgeRequest}
    {before after : Caller width} {result : Edge} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (started : beginEdge request before = (handle, .ready result, after)) :
    ∃ actual : SourceCurrentAllocatedPartialGraph.EdgeCall budget request before result after,
      SourceCurrentAllocatedPartialSourceReads.EdgeCallReads formulas solver actual memos memos ∧
      SourceCurrentAllocatedPartialWorker.edgeCall 0 0 0 0 0 0 0 0 0 0 budget request before = .done result after ∧
      Post formulas solver inventory before after memos ∧
      Resident after.checked.native.machine.heap result ∧ EdgeLaw formulas solver request result := by
  obtain ⟨post, available, law⟩ := SourceCurrentAllocatedPartialCallSteps.edge_hit formulas solver initial inherited resident started
  exact ⟨.hit started, .hit (started := started),
    SourceCurrentAllocatedPartialWorker.edgeCall_ready 0 0 0 0 0 0 0 0 0 0 budget request before after handle result started,
    post, available, law⟩

end MicroCFTA.SourceCurrentAllocatedPartialWorkerLeafActual
