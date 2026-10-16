import MicroCFTA.SourceCurrentAllocatedPartialFrames

namespace MicroCFTA.SourceCurrentAllocatedPartialFramesProbes
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph SourceCurrentAllocatedPartialFrames
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

-- The actual recursive body preserves its own newly started node cell until finish.
theorem node_owner_completed (budget : Nat) (request owner : NodeRequest) (handle : Nat) (result : Node)
    (before running middle : Caller width) (valid : SourceCurrentAllocatedPartialState.Valid before)
    (started : beginNode request before = (handle, .evaluate owner, running))
    (body : NodeBody budget owner running result middle) :
    let after := finishNode handle result middle
    NodeCall budget request before result after ∧ Frame before after ∧
      after.nodeResults.cells handle = some ⟨owner, .returned result⟩ ∧ owner.key = request.key := by
  have protocol := Protocol.of_valid valid
  have first := beginNode_frame request before protocol
  rw [started] at first
  have ownerCell := beginNode_owner request before handle owner running protocol started
  have bodyFrame := node_body body first.valid
  have retained := bodyFrame.node_running handle owner ownerCell.1
  have actual : NodeCall budget request before result (finishNode handle result middle) := .evaluate started body
  exact ⟨actual, node_call actual protocol, finishNode_returned handle owner result middle retained, ownerCell.2⟩

-- The independent edge family retains its own exact request through the reached parent body.
theorem edge_owner_completed (budget : Nat) (request owner : EdgeRequest) (handle : Nat) (result : Edge)
    (before running middle : Caller width) (valid : SourceCurrentAllocatedPartialState.Valid before)
    (started : beginEdge request before = (handle, .evaluate owner, running))
    (body : EdgeBody budget owner running result middle) :
    let after := finishEdge handle result middle
    EdgeCall budget request before result after ∧ Frame before after ∧
      after.edgeResults.cells handle = some ⟨owner, .returned result⟩ ∧ owner.key = request.key := by
  have protocol := Protocol.of_valid valid
  have first := beginEdge_frame request before protocol
  rw [started] at first
  have ownerCell := beginEdge_owner request before handle owner running protocol started
  have bodyFrame := edge_body body first.valid
  have retained := bodyFrame.edge_running handle owner ownerCell.1
  have actual : EdgeCall budget request before result (finishEdge handle result middle) := .evaluate started body
  exact ⟨actual, edge_call actual protocol, finishEdge_returned handle owner result middle retained, ownerCell.2⟩

-- Two actual indexed recursive calls protect running and returned cells in both families.
theorem two_calls_cross_family (budget index : Nat) (combined : EqValue)
    (left right first second : Node) (before middle after : Caller width)
    (head : NodeCall budget ⟨(descend before combined index).1, left⟩
      (descend before combined index).2 first middle)
    (tail : NodeCall budget ⟨(descend middle combined (index + 1)).1, right⟩
      (descend middle combined (index + 1)).2 second after)
    (valid : SourceCurrentAllocatedPartialState.Valid before)
    (nodeHandle edgeHandle nodeDone edgeDone : Nat) (nodeOwner : NodeRequest) (edgeOwner : EdgeRequest)
    (oldNode : Node) (oldEdge : Edge)
    (nodeRunning : before.nodeResults.cells nodeHandle = some ⟨nodeOwner, .evaluating⟩)
    (edgeRunning : before.edgeResults.cells edgeHandle = some ⟨edgeOwner, .evaluating⟩)
    (nodeReturned : before.nodeResults.cells nodeDone = some ⟨nodeOwner, .returned oldNode⟩)
    (edgeReturned : before.edgeResults.cells edgeDone = some ⟨edgeOwner, .returned oldEdge⟩) :
    Walk budget combined index [left, right] before [first, second] after ∧
      after.nodeResults.cells nodeHandle = some ⟨nodeOwner, .evaluating⟩ ∧
      after.edgeResults.cells edgeHandle = some ⟨edgeOwner, .evaluating⟩ ∧
      after.nodeResults.cells nodeDone = some ⟨nodeOwner, .returned oldNode⟩ ∧
      after.edgeResults.cells edgeDone = some ⟨edgeOwner, .returned oldEdge⟩ ∧
      Cache.Extends before.nodeResults.table after.nodeResults.table ∧
      Cache.Extends before.edgeResults.table after.edgeResults.table := by
  have actual : Walk budget combined index [left, right] before [first, second] after := .cons head (.cons tail .nil)
  have framed := walk actual (Protocol.of_valid valid)
  exact ⟨actual, framed.node_running _ _ nodeRunning, framed.edge_running _ _ edgeRunning,
    framed.node_returned _ _ _ nodeReturned, framed.edge_returned _ _ _ edgeReturned,
    framed.node_keys, framed.edge_keys⟩

-- A completed nested node call cannot finish an already active reduced-edge ancestor.
theorem node_call_protects_edge_ancestor (budget : Nat) (request : NodeRequest) (before after : Caller width)
    (result : Node) (actual : NodeCall budget request before result after) (valid : Protocol before)
    (handle : Nat) (owner : EdgeRequest)
    (running : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩)
    (candidate : EdgeRequest) (published : before.edgeResults.table candidate.key = some handle) :
    after.edgeResults.cells handle = some ⟨owner, .evaluating⟩ ∧
      beginEdge candidate after = (handle, .busy, after) ∧
      ∀ edge final, ¬ EdgeCall budget candidate after edge final := by
  have framed := node_call actual valid
  have retained := framed.edge_running handle owner running
  have busy := beginEdge_busy candidate owner after handle (framed.edge_keys _ _ published) retained
  refine ⟨retained, busy, ?_⟩
  intro edge final complete
  exact complete.not_busy busy

end MicroCFTA.SourceCurrentAllocatedPartialFramesProbes

#print axioms MicroCFTA.SourceCurrentAllocatedPartialFramesProbes.node_owner_completed
#print axioms MicroCFTA.SourceCurrentAllocatedPartialFramesProbes.edge_owner_completed
#print axioms MicroCFTA.SourceCurrentAllocatedPartialFramesProbes.two_calls_cross_family
#print axioms MicroCFTA.SourceCurrentAllocatedPartialFramesProbes.node_call_protects_edge_ancestor
#check @MicroCFTA.SourceCurrentAllocatedPartialFramesProbes.node_owner_completed
#check @MicroCFTA.SourceCurrentAllocatedPartialFramesProbes.edge_owner_completed
#check @MicroCFTA.SourceCurrentAllocatedPartialFramesProbes.two_calls_cross_family
#check @MicroCFTA.SourceCurrentAllocatedPartialFramesProbes.node_call_protects_edge_ancestor
