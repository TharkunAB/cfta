import MicroCFTA.SourceCurrentAllocatedPartialChecks

namespace MicroCFTA.PartialChecksKernels
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialState (beginNode beginEdge finishNode finishEdge)
open SourceCurrentAllocatedPartialChecks
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "NodeReq" => SourceCurrentAllocatedPartialState.NodeRequest
local notation "EdgeReq" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
variable {width budget : Nat}

/-- A nested evaluated ordinary node supplies checks at the actual first edge owner. -/
theorem nested_evaluated_owner
    {request : NodeReq} {inherited : EqValue} {before running : Caller width} {nodeHandle : Nat}
    {entry : Interned InternedBinderProtocol.NodeKey} {depth : Nat} {free : List InternedBinderProtocol.Reference}
    {original : EdgeValue Symbol Guard} {originals : List (EdgeValue Symbol Guard)}
    {owner : EdgeReq} {edgeHandle : Nat} {edgeRunning : Caller width}
    {narrowed result : EdgeValue Symbol Guard} {edgeMiddle afterChildren afterRows : Caller width}
    {results : List (EdgeValue Symbol Guard)}
    (nodeStarted : beginNode request before = (nodeHandle, (.evaluate ⟨inherited, .node entry (original :: originals) depth free⟩, running)))
    (edgeStarted : beginEdge ⟨inherited, original⟩ running = (edgeHandle, (.evaluate owner, edgeRunning)))
    (body : EdgeBody budget owner edgeRunning narrowed edgeMiddle)
    (children : Descendants budget inherited narrowed (finishEdge edgeHandle narrowed edgeMiddle) result afterChildren)
    (tail : Rows budget inherited originals afterChildren results afterRows)
    (checks : Checks (nodeCallTrace (NodeCall.evaluate nodeStarted
      (NodeBody.ordinary (entry := entry) (depth := depth) (free := free)
        (Rows.cons (.evaluate edgeStarted body) children tail))))) :
    SourceCurrentAllocatedPartialEdgeActual.Ranges budget owner edgeRunning := by
  have nodeBodyChecks := checks.restrict (.node_evaluate nodeStarted
    (NodeBody.ordinary (entry := entry) (depth := depth) (free := free)
      (Rows.cons (.evaluate edgeStarted body) children tail)))
  have rowChecks := nodeBodyChecks.restrict (.node_ordinary (Rows.cons (.evaluate edgeStarted body) children tail))
  have edgeChecks := rowChecks.restrict (.rows_edge (.evaluate edgeStarted body) children tail)
  exact (edgeChecks.restrict (.edge_evaluate edgeStarted body)).edge_body

/-- Row suffix and descendant checks use the returned edge and each exact reached state. -/
theorem returned_edge_descendants_and_tail
    {inherited : EqValue} {original narrowed result : EdgeValue Symbol Guard}
    {originals results : List (EdgeValue Symbol Guard)} {before middle afterChildren after : Caller width}
    (edge : EdgeCall budget ⟨inherited, original⟩ before narrowed middle)
    (children : Descendants budget inherited narrowed middle result afterChildren)
    (tail : Rows budget inherited originals afterChildren results after)
    (checks : Checks (rowsTrace (.cons edge children tail))) :
    Checks (edgeCallTrace edge) ∧ Checks (descendantsTrace children) ∧ Checks (rowsTrace tail) :=
  ⟨checks.restrict (.rows_edge edge children tail), checks.restrict (.rows_descendants edge children tail),
    checks.restrict (.rows_tail edge children tail)⟩

/-- A literal inherited prefix reaches its live indexed head and next-index tail. -/
theorem live_descendants_head_tail
    {edge : EdgeValue Symbol Guard} {inherited : EqValue} {before : Caller width} {identity : Nat}
    {records : List SourceEqualityClassOrder.Record} {value result : Value Symbol Guard}
    {values results : List (Value Symbol Guard)} {middle after : Caller width}
    (shape : edge.children = value :: values)
    (combined : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited before.checked.operations).1 =
      .ok (some (.live identity records)))
    (head : NodeCall budget ⟨(descend (prefixState before edge inherited) (.live identity records) 0).1, value⟩
      (descend (prefixState before edge inherited) (.live identity records) 0).2 result middle)
    (tail : Walk budget (.live identity records) (0 + 1) values middle results after)
    (checks : Checks (descendantsTrace (Descendants.run combined
      (Children.live (shape ▸ Walk.cons head tail))))) :
    Checks (nodeCallTrace head) ∧ Checks (walkTrace tail) := by
  have childrenChecks := checks.restrict (.descendants_children combined (Children.live (shape ▸ Walk.cons head tail)))
  have actualChecks := childrenChecks.restrict (.children_walk (shape ▸ Walk.cons head tail))
  have walkChecks : Checks (walkTrace (Walk.cons head tail)) := by
    simpa only [shape] using actualChecks
  exact ⟨walkChecks.restrict (.walk_head head tail), walkChecks.restrict (.walk_tail head tail)⟩

/-- A ready edge hit supplies a vacuous call range plan without a body plan. -/
theorem ready_hit_no_ranges {request : EdgeReq} {before running : Caller width} {handle : Nat}
    {result : EdgeValue Symbol Guard}
    (started : beginEdge request before = (handle, (.ready result, running))) :
    SourceCurrentAllocatedPartialEdgeActual.CallRanges budget request before := by
  intro other owner reached evaluated
  rw [started] at evaluated
  cases evaluated

/-- Equal node wrappers retain all physical request and state metadata. -/
theorem node_metadata
    {firstRequest secondRequest : NodeReq} {firstBefore secondBefore firstAfter secondAfter : Caller width}
    {firstResult secondResult : Value Symbol Guard}
    {first : NodeCall budget firstRequest firstBefore firstResult firstAfter}
    {second : NodeCall budget secondRequest secondBefore secondResult secondAfter}
    (same : nodeCallTrace first = nodeCallTrace second) :
    firstRequest = secondRequest ∧ firstBefore = secondBefore ∧ firstResult = secondResult ∧ firstAfter = secondAfter := by
  cases same
  exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms nested_evaluated_owner
#print axioms returned_edge_descendants_and_tail
#print axioms live_descendants_head_tail
#print axioms ready_hit_no_ranges
#print axioms node_metadata
set_option pp.explicit true
#check @nested_evaluated_owner
#check @returned_edge_descendants_and_tail
#check @live_descendants_head_tail
#check @ready_hit_no_ranges
#check @node_metadata
end MicroCFTA.PartialChecksKernels
