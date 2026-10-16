import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEntries

namespace MicroCFTA.OuterEntryKernels
open InternedConstructorTemplates
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedFiniteOrdinaryOuterEntries
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

/-- The first parent checks precede its own body, without any completed child graph. -/
theorem first_parent_checks
    {budget nodeHandle edgeHandle : Nat} {candidate : NodeRequest} {owner : EdgeRequest}
    {inherited : EqValue} {entry : Cache.Interned InternedBinderProtocol.NodeKey}
    {original : Edge} {originals : List Edge}
    {depth : Nat} {free : List InternedBinderProtocol.Reference}
    {before running parentState : Caller width}
    (plan : Plan budget (.nodeCall candidate before))
    (nodeStart : beginNode candidate before =
      (nodeHandle, .evaluate ⟨inherited, .node entry (original :: originals) depth free⟩, running))
    (edgeStart : beginEdge ⟨inherited, original⟩ running = (edgeHandle, .evaluate owner, parentState)) :
    SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget owner parentState := by
  exact plan owner parentState (.trans (.direct (.node_evaluate nodeStart))
    (.trans (.direct .node_ordinary) (.trans (.direct .rows_edge) (.direct (.edge_evaluate edgeStart)))))

/-- Tail checks use the actual earlier edge and descendants return, including every warm table. -/
theorem tail_parent_checks
    {budget handle : Nat} {inherited : EqValue} {original next : Edge} {rest : List Edge}
    {narrowed result : Edge} {owner : EdgeRequest} {before middle afterChildren running : Caller width}
    (plan : Plan budget (.rows inherited (original :: next :: rest) before))
    (edge : EdgeCall budget ⟨inherited, original⟩ before narrowed middle)
    (children : Descendants budget inherited narrowed middle result afterChildren)
    (started : beginEdge ⟨inherited, next⟩ afterChildren = (handle, .evaluate owner, running)) :
    SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget owner running := by
  exact (plan.restrict (.trans (.direct (.rows_tail edge children)) (.direct .rows_edge))).edge_call_ranges
    handle owner running started

/-- A later indexed node inherits checks at the exact earlier node return and next descent. -/
theorem next_index_checks
    {budget index : Nat} {combined : EqValue} {value next result : Node} {rest : List Node}
    {before middle : Caller width}
    (plan : Plan budget (.walk combined index (value :: next :: rest) before))
    (earlier : NodeCall budget ⟨(descend before combined index).1, value⟩
      (descend before combined index).2 result middle) :
    Plan budget (.nodeCall ⟨(descend middle combined (index + 1)).1, next⟩
      (descend middle combined (index + 1)).2) := by
  exact plan.restrict (.trans (.direct (.walk_tail earlier)) (.direct .walk_node))

/-- Contradictory children have no entered child control. -/
theorem contradiction_has_no_child_step
    {budget : Nat} {values : List Node} {before : Caller width} {last : Entry width} :
    ¬ Step budget (.children .contradiction values before) last := by
  intro actual
  cases actual

#print axioms first_parent_checks
#check @first_parent_checks
#print axioms tail_parent_checks
#check @tail_parent_checks
#print axioms next_index_checks
#check @next_index_checks
#print axioms contradiction_has_no_child_step
#check @contradiction_has_no_child_step

end MicroCFTA.OuterEntryKernels
