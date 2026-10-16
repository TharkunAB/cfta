import MicroCFTA.SourceCurrentAllocatedPartialGraph

namespace MicroCFTA.SourceCurrentAllocatedPartialGraphProbes
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

-- Each index reads the actual preceding operation state before its recursive request.
theorem two_actual_indices (budget index : Nat) (combined : EqValue) (first second left right : Node)
    (before middle after : Caller width)
    (head : NodeCall budget ⟨(descend before combined index).1, first⟩
      (descend before combined index).2 left middle)
    (tail : NodeCall budget ⟨(descend middle combined (index + 1)).1, second⟩
      (descend middle combined (index + 1)).2 right after) :
    Walk budget combined index [first, second] before [left, right] after ∧
      (descend before combined index).1 = (SourceEqualityConstraintMemoAllocation.descend combined index before.checked.operations).1 ∧
      (descend middle combined (index + 1)).2.checked.operations =
        (SourceEqualityConstraintMemoAllocation.descend combined (index + 1) middle.checked.operations).2 ∧
      (descend middle combined (index + 1)).2.nodeResults = middle.nodeResults ∧
      (descend middle combined (index + 1)).2.edgeResults = middle.edgeResults := by
  exact ⟨.cons head (.cons tail .nil), rfl, rfl, rfl, rfl⟩

-- Descendants use the returned edge's raw field; their equal-arity rebuild keeps that field.
theorem returned_edge_fields (budget : Nat) (inherited combined : EqValue) (returned : Edge)
    (before middle : Caller width) (results : List Node)
    (prefixDone : (SourceCurrentAllocatedInheritedPrefix.run returned.entry.key.constraint inherited before.checked.operations).1 =
      .ok (some combined))
    (children : Children budget combined returned.children (prefixState before returned inherited) results middle)
    (facts : InternedNestedFacts.Facts middle.checked.native.machine.heap)
    (available : InternedNestedProvenance.Values middle.checked.native.machine.heap results) :
    let built := SourceCurrentAllocatedRawRebuild.edge returned results middle.checked
    Descendants budget inherited returned before built.1
        (advance middle built.2 middle.fourth middle.merge) ∧
      built.1.entry.key.symbol = returned.entry.key.symbol ∧
      built.1.entry.key.constraint = returned.entry.key.constraint ∧ built.1.children = results ∧
      ∀ checked : Symbol → List Node → Guard → Work Symbol Guard Edge,
        built =
          let actual := run (EqualityLeafProjectionSetChildren.setChildren checked returned results) middle.checked.native.machine.heap
          (actual.1, SourceCurrentAllocatedQueryMemo.advancePhysical middle.checked ⟨actual.2, middle.checked.operations⟩) := by
  have fields := MergedPhysicalGroupEdges.makeEdge_fields middle.checked.native.machine.heap facts
    returned.entry.key.symbol returned.entry.key.constraint results available
  exact ⟨.run prefixDone children, fields.1, fields.2.1, fields.2.2,
    fun checked => SourceCurrentAllocatedRawRebuild.edge_same_arity checked returned results middle.checked children.length⟩

-- Ordered rows finish each returned edge's descendants before starting the next edge.
theorem ordered_two_rows (budget : Nat) (inherited : EqValue) (first second narrowedFirst narrowedSecond left right : Edge)
    (before afterFirst afterFirstChildren afterSecond afterSecondChildren : Caller width)
    (firstCall : EdgeCall budget ⟨inherited, first⟩ before narrowedFirst afterFirst)
    (firstChildren : Descendants budget inherited narrowedFirst afterFirst left afterFirstChildren)
    (secondCall : EdgeCall budget ⟨inherited, second⟩ afterFirstChildren narrowedSecond afterSecond)
    (secondChildren : Descendants budget inherited narrowedSecond afterSecond right afterSecondChildren)
    (entry : Interned InternedBinderProtocol.NodeKey) (depth : Nat) (free : List InternedBinderProtocol.Reference) :
    Rows budget inherited [first, second] before [left, right] afterSecondChildren ∧
      [left, right].length = [first, second].length ∧
      NodeBody budget ⟨inherited, .node entry [first, second] depth free⟩ before
        (SourceCurrentAllocatedRawRebuild.modify (.node entry [first, second] depth free)
          [first, second] [left, right] afterSecondChildren.checked).1
        (advance afterSecondChildren
          (SourceCurrentAllocatedRawRebuild.modify (.node entry [first, second] depth free)
            [first, second] [left, right] afterSecondChildren.checked).2
          afterSecondChildren.fourth afterSecondChildren.merge) ∧
      ([left, right].map (fun edge => edge.entry.identity) = [first, second].map (fun edge => edge.entry.identity) →
        SourceCurrentAllocatedRawRebuild.modify (.node entry [first, second] depth free)
          [first, second] [left, right] afterSecondChildren.checked =
            (.node entry [first, second] depth free, afterSecondChildren.checked)) := by
  have actual : Rows budget inherited [first, second] before [left, right] afterSecondChildren :=
    .cons firstCall firstChildren (.cons secondCall secondChildren .nil)
  exact ⟨actual, actual.length, .ordinary actual, fun same =>
    SourceCurrentAllocatedRawRebuild.modify_unchanged _ _ _ _ same⟩

-- Running cells in either result family are observations, not successful completed calls.
theorem both_busy_excluded (budget : Nat) (before : Caller width) (node : NodeRequest) (edge : EdgeRequest)
    (nodeOwner : NodeRequest) (edgeOwner : EdgeRequest) (nodeHandle edgeHandle : Nat)
    (nodeKey : before.nodeResults.table node.key = some nodeHandle)
    (nodeRunning : before.nodeResults.cells nodeHandle = some ⟨nodeOwner, .evaluating⟩)
    (edgeKey : before.edgeResults.table edge.key = some edgeHandle)
    (edgeRunning : before.edgeResults.cells edgeHandle = some ⟨edgeOwner, .evaluating⟩) :
    (∀ result after, ¬ NodeCall budget node before result after) ∧
      (∀ result after, ¬ EdgeCall budget edge before result after) := by
  constructor
  · intro result after actual
    exact actual.not_busy (beginNode_busy node nodeOwner before nodeHandle nodeKey nodeRunning)
  · intro result after actual
    exact actual.not_busy (beginEdge_busy edge edgeOwner before edgeHandle edgeKey edgeRunning)

-- A fresh raw reference must evaluate its own body, which has the source error and no success.
theorem fresh_reference_error (budget : Nat) (before : Caller width) (inherited : EqValue)
    (name : InternedBinderProtocol.Reference)
    (missing : before.nodeResults.table (NodeRequest.key ⟨inherited, .reference name⟩) = none) :
    ∀ result after, ¬ NodeCall budget ⟨inherited, .reference name⟩ before result after := by
  have fresh : beginNode ⟨inherited, .reference name⟩ before =
      (before.nodeResults.next, .evaluate ⟨inherited, .reference name⟩,
        { before with nodeResults  := (FlatMemoThunk.setStatus before.nodeResults.next .evaluating
            (FlatMemoThunk.lookupOrInsert (NodeRequest.key ⟨inherited, .reference name⟩)
              ⟨inherited, .reference name⟩ before.nodeResults).2) }) := by
    simp [beginNode, FlatMemoThunk.lookupOrInsert, missing, FlatMemoThunk.demand, FlatMemoThunk.setStatus, put]
  intro result after actual
  cases actual with
  | hit started =>
      have impossible := congrArg (fun value => value.2.1) (fresh.symm.trans started)
      cases impossible
  | evaluate started body =>
      have original := FlatMemoThunk.Observation.evaluate.inj
        (congrArg (fun value => value.2.1) (fresh.symm.trans started))
      rw [← original] at body
      exact NodeBody.reference_error body

end MicroCFTA.SourceCurrentAllocatedPartialGraphProbes

#print axioms MicroCFTA.SourceCurrentAllocatedPartialGraphProbes.two_actual_indices
#print axioms MicroCFTA.SourceCurrentAllocatedPartialGraphProbes.returned_edge_fields
#print axioms MicroCFTA.SourceCurrentAllocatedPartialGraphProbes.ordered_two_rows
#print axioms MicroCFTA.SourceCurrentAllocatedPartialGraphProbes.both_busy_excluded
#print axioms MicroCFTA.SourceCurrentAllocatedPartialGraphProbes.fresh_reference_error
#check @MicroCFTA.SourceCurrentAllocatedPartialGraphProbes.two_actual_indices
#check @MicroCFTA.SourceCurrentAllocatedPartialGraphProbes.returned_edge_fields
#check @MicroCFTA.SourceCurrentAllocatedPartialGraphProbes.ordered_two_rows
#check @MicroCFTA.SourceCurrentAllocatedPartialGraphProbes.both_busy_excluded
#check @MicroCFTA.SourceCurrentAllocatedPartialGraphProbes.fresh_reference_error
