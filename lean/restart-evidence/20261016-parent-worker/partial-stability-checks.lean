import MicroCFTA.SourceCurrentAllocatedPartialWorkerStability

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.bind_done_iff
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.bind_done_iff
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.nodeCall_done_stable
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.nodeCall_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.nodeBody_done_stable
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.nodeBody_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.edgeCall_done_stable
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.edgeCall_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.edgeBody_done_stable
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.edgeBody_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.rows_done_stable
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.rows_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.descendants_done_stable
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.descendants_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.children_done_stable
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.children_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.walk_done_stable
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.walk_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.nodeCall_done_unique
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.nodeCall_done_unique
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.nodeBody_done_unique
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.nodeBody_done_unique
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.edgeCall_done_unique
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.edgeCall_done_unique
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.edgeBody_done_unique
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.edgeBody_done_unique
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.rows_done_unique
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.rows_done_unique
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.descendants_done_unique
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.descendants_done_unique
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.children_done_unique
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.children_done_unique
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.walk_done_unique
#check @MicroCFTA.SourceCurrentAllocatedPartialWorkerStability.walk_done_unique

namespace PartialStabilityChecks
open MicroCFTA
open Cache Language InternedConstructorTemplates
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedPartialWorkerStability
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

 theorem ready_node_zero (budget : Nat) (request : NodeRequest) (before after : Caller width)
    (handle : Nat) (result : Node) (started : beginNode request before = (handle, .ready result, after))
    (fuel g s r e p h m c n : Nat) :
    nodeCall fuel g s r e p h m c n budget request before = .done result after := by
  have zero := nodeCall_ready 0 0 0 0 0 0 0 0 0 0 budget request before after handle result started
  exact nodeCall_done_stable zero (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

 theorem ready_edge_zero (budget : Nat) (request : EdgeRequest) (before after : Caller width)
    (handle : Nat) (result : Edge) (started : beginEdge request before = (handle, .ready result, after))
    (fuel g s r e p h m c n : Nat) :
    edgeCall fuel g s r e p h m c n budget request before = .done result after := by
  have zero := edgeCall_ready 0 0 0 0 0 0 0 0 0 0 budget request before after handle result started
  exact edgeCall_done_stable zero (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

 theorem binder_zero (budget : Nat) (inherited : EqValue)
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Node)
    (before : Caller width) (result : Node) (heap : State Symbol Guard)
    (built : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.checked.native.machine.heap = .done result heap)
    (fuel g s r e p h m c n : Nat) :
    nodeBody fuel g s r e p h m c n budget ⟨inherited, .mu entry body depth ordinary⟩ before =
      .done result (advance before
        (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨heap, before.checked.operations⟩)
        before.fourth before.merge) := by
  have zero : nodeBody 0 0 0 0 0 0 0 0 0 0 budget ⟨inherited, .mu entry body depth ordinary⟩ before =
      .done result (advance before
        (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨heap, before.checked.operations⟩)
        before.fourth before.merge) := by simp only [nodeBody, built]
  exact nodeBody_done_stable zero (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

 theorem parent_rejection_zero (budget : Nat) (request : EdgeRequest) (before : Caller width)
    (test : SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = true)
    (fuel g s r e p h m c n : Nat) :
    edgeBody fuel g s r e p h m c n budget request before =
      .done (SourceCurrentAllocatedMkEdge.reject request.value.entry.key.symbol before.checked).1
        (advance before (SourceCurrentAllocatedMkEdge.reject request.value.entry.key.symbol before.checked).2
          before.fourth before.merge) := by
  have rejected := SourceCurrentAllocatedParentWorker.edge_rejected 0 0 0 0 0 0 0 0 0 budget
    request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
    before.checked before.fourth before.merge test
  have zero : edgeBody 0 0 0 0 0 0 0 0 0 0 budget request before =
      .done (SourceCurrentAllocatedMkEdge.reject request.value.entry.key.symbol before.checked).1
        (advance before (SourceCurrentAllocatedMkEdge.reject request.value.entry.key.symbol before.checked).2
          before.fourth before.merge) := by simp only [edgeBody, rejected]
  exact edgeBody_done_stable zero (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

 theorem contradictory_children_zero (budget : Nat) (values : List Node) (before : Caller width)
    (fuel g s r e p h m c n : Nat) :
    children fuel g s r e p h m c n budget .contradiction values before =
      .done (EqualityLeafProjectionRuntimeEmpty.erase values) before := by
  have zero : children 0 0 0 0 0 0 0 0 0 0 budget .contradiction values before =
      .done (EqualityLeafProjectionRuntimeEmpty.erase values) before := by simp only [children]
  exact children_done_stable zero (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

 theorem indexed_walk_cons {fuel larger budget : Nat} (enough : fuel ≤ larger)
    (combined : EqValue) (index : Nat) (value : Node) (rest : List Node)
    (before middle after : Caller width) (result : Node) (results : List Node)
    (head : nodeCall fuel fuel fuel fuel fuel fuel fuel fuel fuel fuel budget
      ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1, value⟩
      (SourceCurrentAllocatedPartialGraph.descend before combined index).2 = .done result middle)
    (tail : walk fuel fuel fuel fuel fuel fuel fuel fuel fuel fuel budget combined (index + 1) rest middle = .done results after) :
    walk (larger + 1) larger larger larger larger larger larger larger larger larger budget combined index (value :: rest) before =
      .done (result :: results) after := by
  have base : walk (fuel + 1) fuel fuel fuel fuel fuel fuel fuel fuel fuel budget combined index (value :: rest) before =
      .done (result :: results) after := by simp only [walk, head, tail, Outcome.bind]
  exact walk_done_stable base (Nat.succ_le_succ enough) enough enough enough enough enough enough enough enough enough

 theorem ordered_rows_cons {fuel larger budget : Nat} (enough : fuel ≤ larger)
    (inherited : EqValue) (original : Edge) (rest : List Edge) (narrowed result : Edge) (results : List Edge)
    (before middle current after : Caller width)
    (parent : edgeCall fuel fuel fuel fuel fuel fuel fuel fuel fuel fuel budget ⟨inherited, original⟩ before = .done narrowed middle)
    (descend : descendants fuel fuel fuel fuel fuel fuel fuel fuel fuel fuel budget inherited narrowed middle = .done result current)
    (tail : rows fuel fuel fuel fuel fuel fuel fuel fuel fuel fuel budget inherited rest current = .done results after) :
    rows (larger + 1) larger larger larger larger larger larger larger larger larger budget inherited (original :: rest) before =
      .done (result :: results) after := by
  have base : rows (fuel + 1) fuel fuel fuel fuel fuel fuel fuel fuel fuel budget inherited (original :: rest) before =
      .done (result :: results) after := by simp only [rows, parent, descend, tail, Outcome.bind]
  exact rows_done_stable base (Nat.succ_le_succ enough) enough enough enough enough enough enough enough enough enough

 theorem inherited_prefix_then_children {fuel larger budget : Nat} (enough : fuel ≤ larger)
    (inherited combined : EqValue) (original : Edge) (before middle : Caller width) (values : List Node)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (entered : SourceCurrentAllocatedInheritedPrefix.run original.entry.key.constraint inherited before.checked.operations =
      (.ok (some combined), operations))
    (child : children fuel fuel fuel fuel fuel fuel fuel fuel fuel fuel budget combined original.children
      (advance before (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked
        ⟨before.checked.native.machine.heap, operations⟩) before.fourth before.merge) = .done values middle) :
    descendants larger larger larger larger larger larger larger larger larger larger budget inherited original before =
      .done (SourceCurrentAllocatedRawRebuild.edge original values middle.checked).1
        (advance middle (SourceCurrentAllocatedRawRebuild.edge original values middle.checked).2 middle.fourth middle.merge) := by
  have base : descendants fuel fuel fuel fuel fuel fuel fuel fuel fuel fuel budget inherited original before =
      .done (SourceCurrentAllocatedRawRebuild.edge original values middle.checked).1
        (advance middle (SourceCurrentAllocatedRawRebuild.edge original values middle.checked).2 middle.fourth middle.merge) := by
    simp only [descendants, entered, child, Outcome.bind]
  exact descendants_done_stable base enough enough enough enough enough enough enough enough enough enough

 theorem incomparable_returns_keep_all_tables
    {fuel F g s r e p h m c n G S R E P H M C N budget : Nat}
    {request : NodeRequest} {before after later : Caller width} {first second : Node}
    (one : nodeCall fuel g s r e p h m c n budget request before = .done first after)
    (two : nodeCall F G S R E P H M C N budget request before = .done second later) :
    first = second ∧ after.checked = later.checked ∧ after.nodeResults = later.nodeResults ∧
      after.edgeResults = later.edgeResults ∧ after.fourth = later.fourth ∧ after.merge = later.merge := by
  obtain ⟨same, rfl⟩ := nodeCall_done_unique one two
  exact ⟨same, rfl, rfl, rfl, rfl, rfl⟩

end PartialStabilityChecks

#print axioms PartialStabilityChecks.ready_node_zero
#check @PartialStabilityChecks.ready_node_zero
#print axioms PartialStabilityChecks.ready_edge_zero
#check @PartialStabilityChecks.ready_edge_zero
#print axioms PartialStabilityChecks.binder_zero
#check @PartialStabilityChecks.binder_zero
#print axioms PartialStabilityChecks.parent_rejection_zero
#check @PartialStabilityChecks.parent_rejection_zero
#print axioms PartialStabilityChecks.contradictory_children_zero
#check @PartialStabilityChecks.contradictory_children_zero
#print axioms PartialStabilityChecks.indexed_walk_cons
#check @PartialStabilityChecks.indexed_walk_cons
#print axioms PartialStabilityChecks.ordered_rows_cons
#check @PartialStabilityChecks.ordered_rows_cons
#print axioms PartialStabilityChecks.inherited_prefix_then_children
#check @PartialStabilityChecks.inherited_prefix_then_children
#print axioms PartialStabilityChecks.incomparable_returns_keep_all_tables
#check @PartialStabilityChecks.incomparable_returns_keep_all_tables
