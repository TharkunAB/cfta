import MicroCFTA.SourceCurrentAllocatedPartialState

namespace MicroCFTA.SourceCurrentAllocatedPartialStateProbes
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "MergeMemo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "CallerState" => SourceCurrentAllocatedPartialState.State
variable {width : Nat}

-- An active outer request remains busy while the separate reduced-edge family starts.
theorem nested_families (checked : Checked width) (merge : MergeMemo) (fourth : Fourth)
    (node : NodeRequest) (edge : EdgeRequest) :
    let start := initial checked merge fourth
    let first := (beginNode node start).2.2
    let second := (beginEdge edge first).2.2
    (beginNode node start).1 = 0 ∧ (beginNode node start).2.1 = .evaluate node ∧
    (beginEdge edge first).1 = 0 ∧ (beginEdge edge first).2.1 = .evaluate edge ∧
    beginNode node second = (0, .busy, second) ∧
    second.checked = checked ∧ second.merge = merge ∧ second.fourth = fourth := by
  simp [beginNode, beginEdge, initial, FlatMemoThunk.lookupOrInsert, FlatMemoThunk.empty,
    FlatMemoThunk.demand, FlatMemoThunk.setStatus, Cache.put]

-- Edge completion retains an active node cell, which its own finish then completes.
theorem complete_both (before : CallerState width) (node : NodeRequest) (edge : EdgeRequest)
    (nodeResult : Node) (edgeResult : Edge) (nodeHandle edgeHandle : Nat)
    (nodePublished : before.nodeResults.table node.key = some nodeHandle)
    (edgePublished : before.edgeResults.table edge.key = some edgeHandle)
    (nodeRunning : before.nodeResults.cells nodeHandle = some ⟨node, .evaluating⟩)
    (edgeRunning : before.edgeResults.cells edgeHandle = some ⟨edge, .evaluating⟩) :
    let after := finishNode nodeHandle nodeResult (finishEdge edgeHandle edgeResult before)
    beginNode node after = (nodeHandle, .ready nodeResult, after) ∧
    beginEdge edge after = (edgeHandle, .ready edgeResult, after) ∧
    after.checked = before.checked ∧ after.merge = before.merge ∧ after.fourth = before.fourth := by
  have first := finishEdge_returned edgeHandle edge edgeResult before edgeRunning
  have last := finishNode_returned nodeHandle node nodeResult (finishEdge edgeHandle edgeResult before) nodeRunning
  have nodeTable : (finishNode nodeHandle nodeResult (finishEdge edgeHandle edgeResult before)).nodeResults.table node.key =
      some nodeHandle := by
    simpa only [finishNode, finishEdge, FlatMemoThunk.finish, nodeRunning, FlatMemoThunk.setStatus] using nodePublished
  have edgeTable : (finishNode nodeHandle nodeResult (finishEdge edgeHandle edgeResult before)).edgeResults.table edge.key =
      some edgeHandle := by
    simpa only [finishNode, finishEdge, FlatMemoThunk.finish, edgeRunning, FlatMemoThunk.setStatus] using edgePublished
  exact ⟨beginNode_ready _ _ _ _ _ nodeTable last, beginEdge_ready _ _ _ _ _ edgeTable first, rfl, rfl, rfl⟩

-- Actual checked operation growth retains key links and a previously returned outer winner.
theorem allocation_retains_ready (before : CallerState width) (after : Checked width) (fourth : Fourth) (merge : MergeMemo)
    (valid : Valid before)
    (effects : SourceCurrentConjunctionRowsAllocation.Effects
      (SourceCurrentAllocatedNativeEffects.physical before.checked) (SourceCurrentAllocatedNativeEffects.physical after))
    (candidate original : NodeRequest) (handle : Nat) (result : Node)
    (published : before.nodeResults.table candidate.key = some handle)
    (returned : before.nodeResults.cells handle = some ⟨original, .returned result⟩) :
    Valid (advance before after fourth merge) ∧
    beginNode candidate (advance before after fourth merge) = (handle, .ready result, advance before after fourth merge) :=
  ⟨valid.advance before after fourth merge effects.grows.constraint_growth,
    beginNode_ready _ _ _ _ _ published returned⟩

-- A dangling published handle remains absent; it cannot become a successful cached result.
theorem absent_observation (request : NodeRequest) (before : CallerState width) (handle : Nat)
    (published : before.nodeResults.table request.key = some handle)
    (absent : before.nodeResults.cells handle = none) :
    beginNode request before = (handle, .absent, before) := by
  simp only [beginNode, FlatMemoThunk.lookup_hit _ _ _ _ published, FlatMemoThunk.demand, absent]

end MicroCFTA.SourceCurrentAllocatedPartialStateProbes

#print axioms MicroCFTA.SourceCurrentAllocatedPartialStateProbes.nested_families
#print axioms MicroCFTA.SourceCurrentAllocatedPartialStateProbes.complete_both
#print axioms MicroCFTA.SourceCurrentAllocatedPartialStateProbes.allocation_retains_ready
#print axioms MicroCFTA.SourceCurrentAllocatedPartialStateProbes.absent_observation
#check @MicroCFTA.SourceCurrentAllocatedPartialStateProbes.nested_families
#check @MicroCFTA.SourceCurrentAllocatedPartialStateProbes.complete_both
#check @MicroCFTA.SourceCurrentAllocatedPartialStateProbes.allocation_retains_ready
#check @MicroCFTA.SourceCurrentAllocatedPartialStateProbes.absent_observation
