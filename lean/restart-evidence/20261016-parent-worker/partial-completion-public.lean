import MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.StableRun
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.StableRun
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.nodeCall_complete
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.nodeCall_complete
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.nodeBody_complete
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.nodeBody_complete
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.edgeCall_complete
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.edgeCall_complete
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.edgeBody_complete
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.edgeBody_complete
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.rows_complete
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.rows_complete
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.descendants_complete
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.descendants_complete
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.children_complete
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.children_complete
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.walk_complete
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion.walk_complete

namespace MicroCFTA.PartialCompletionIndependentProbes
open Language InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker SourceCurrentAllocatedPartialWorkerCompletion
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

-- Ready node results run even with zero outer and lower bounds.
example (budget : Nat) (request : NodeRequest) (before after : Caller width) (handle : Nat) (value : Node)
    (started : beginNode request before = (handle, .ready value, after)) :
    nodeCall 0 0 0 0 0 0 0 0 0 0 budget request before = .done value after :=
  nodeCall_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ started

-- Ready edge results skip the parent worker and all of its lower bounds.
example (budget : Nat) (request : EdgeRequest) (before after : Caller width) (handle : Nat) (value : Edge)
    (started : beginEdge request before = (handle, .ready value, after)) :
    edgeCall 0 0 0 0 0 0 0 0 0 0 budget request before = .done value after :=
  edgeCall_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ started

-- Finite node evaluation executes the stored owner and finishes the selected handle.
example {budget : Nat} {request original : NodeRequest} {before running middle : Caller width} {handle : Nat} {value : Node}
    (started : beginNode request before = (handle, .evaluate original, running))
    (body : SourceCurrentAllocatedPartialGraph.NodeBody budget original running value middle) :
    StableRun (fun f g s r e p h m c n => nodeCall f g s r e p h m c n budget request before)
      value (finishNode handle value middle) := nodeCall_complete (.evaluate started body)

-- Finite edge evaluation keeps its distinct family and exact finish handle.
example {budget : Nat} {request original : EdgeRequest} {before running middle : Caller width} {handle : Nat} {value : Edge}
    (started : beginEdge request before = (handle, .evaluate original, running))
    (body : SourceCurrentAllocatedPartialGraph.EdgeBody budget original running value middle) :
    StableRun (fun f g s r e p h m c n => edgeCall f g s r e p h m c n budget request before)
      value (finishEdge handle value middle) := edgeCall_complete (.evaluate started body)

-- Ordinary reconstruction consumes the same completed rows and their returned full caller.
example {budget : Nat} {inherited : EqValue} {entry : Cache.Interned InternedBinderProtocol.NodeKey}
    {depth : Nat} {free : List InternedBinderProtocol.Reference} {original results : List Edge} {before middle : Caller width}
    (actual : SourceCurrentAllocatedPartialGraph.Rows budget inherited original before results middle) :
    StableRun (fun f g s r e p h m c n => nodeBody f g s r e p h m c n budget ⟨inherited, .node entry original depth free⟩ before)
      (SourceCurrentAllocatedRawRebuild.modify (.node entry original depth free) original results middle.checked).1
      (advance middle (SourceCurrentAllocatedRawRebuild.modify (.node entry original depth free) original results middle.checked).2
        middle.fourth middle.merge) := nodeBody_complete (.ordinary actual)

-- Parent completion uses the actual same-cache field and preserves its exact checked/memo return.
example {budget : Nat} {edge result : Edge} {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
    {inherited : EqValue} {before : Caller width} {checked : SourceEqualityNativeDemand.State width}
    {fourth : SourceCurrentEmptinessMemo.Memo} {merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard}
    (field : SourceEqualityMkEdgeAllocation.contradictory edge.entry.key.constraint = false →
      SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint before.checked.operations.constraints = .ok (some loaded))
    (actual : SourceCurrentAllocatedParentEdge.Edge budget edge.entry.key.symbol edge.entry.key.constraint loaded inherited
      edge.children before.checked before.fourth before.merge result checked fourth merge) :
    StableRun (fun f g s r e p h m c n => edgeBody f g s r e p h m c n budget ⟨inherited, edge⟩ before)
      result (advance before checked fourth merge) := edgeBody_complete (.parent field actual)

-- Row traversal runs each returned parent edge's descendants before the suffix.
example {budget : Nat} {inherited : EqValue} {original narrowed result : Edge} {originals results : List Edge}
    {before middle afterChildren after : Caller width}
    (head : SourceCurrentAllocatedPartialGraph.EdgeCall budget ⟨inherited, original⟩ before narrowed middle)
    (children : SourceCurrentAllocatedPartialGraph.Descendants budget inherited narrowed middle result afterChildren)
    (rest : SourceCurrentAllocatedPartialGraph.Rows budget inherited originals afterChildren results after) :
    StableRun (fun f g s r e p h m c n => rows f g s r e p h m c n budget inherited (original :: originals) before)
      (result :: results) after := rows_complete (.cons head children rest)

-- The literal inherited prefix starts child execution at its own operation return.
example {budget : Nat} {edge : Edge} {inherited payload : EqValue} {before middle : Caller width} {results : List Node}
    (combined : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited before.checked.operations).1 =
      .ok (some payload))
    (child : SourceCurrentAllocatedPartialGraph.Children budget payload edge.children
      (SourceCurrentAllocatedPartialGraph.prefixState before edge inherited) results middle) :
    StableRun (fun f g s r e p h m c n => descendants f g s r e p h m c n budget inherited edge before)
      (SourceCurrentAllocatedRawRebuild.edge edge results middle.checked).1
      (advance middle (SourceCurrentAllocatedRawRebuild.edge edge results middle.checked).2 middle.fourth middle.merge) :=
  descendants_complete (.run combined child)

-- Inherited contradiction erases unresolved children without a recursive call or outer fuel.
example (budget : Nat) (name : InternedBinderProtocol.Reference) (before : Caller width) :
    children 0 0 0 0 0 0 0 0 0 0 budget .contradiction [.reference name] before =
      .done (EqualityLeafProjectionRuntimeEmpty.erase [.reference name]) before := by
  simp only [children]

-- Actual indexed descent supplies the next request's inherited payload at the current cache.
example {budget : Nat} {combined : EqValue} {index : Nat} {value result : Node} {values results : List Node}
    {before middle after : Caller width}
    (head : SourceCurrentAllocatedPartialGraph.NodeCall budget
      ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1, value⟩
      (SourceCurrentAllocatedPartialGraph.descend before combined index).2 result middle)
    (rest : SourceCurrentAllocatedPartialGraph.Walk budget combined (index + 1) values middle results after) :
    StableRun (fun f g s r e p h m c n => walk f g s r e p h m c n budget combined index (value :: values) before)
      (result :: results) after := walk_complete (.cons head rest)

-- Binder completion retains the literal reconstruction result and heap, without assuming identity.
example {budget : Nat} {entry : Cache.Interned InternedBinderProtocol.NodeKey} {body : Node}
    {depth ordinary : Node} {before : Caller width} {value : Node} {heap : InternedConstructorTemplates.State Symbol Guard}
    {inherited : EqValue}
    (rebuilt : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.checked.native.machine.heap = .done value heap) :
    StableRun (fun f g s r e p h m c n => nodeBody f g s r e p h m c n budget ⟨inherited, .mu entry body depth ordinary⟩ before)
      value (advance before (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨heap, before.checked.operations⟩)
        before.fourth before.merge) := nodeBody_complete (.binder rebuilt)
end MicroCFTA.PartialCompletionIndependentProbes
