import MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.After
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.After
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.nodeCall
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.nodeCall
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.nodeBody
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.nodeBody
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.edgeCall
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.edgeCall
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.edgeBody
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.edgeBody
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.rows
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.rows
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.descendants
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.descendants
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.children
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.children
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.walk
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.walk
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.after_of_done
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.after_of_done
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.edgeBody_of_done
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.edgeBody_of_done
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.nodeCall_of_evaluate
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.nodeCall_of_evaluate
#print axioms MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.edgeCall_of_evaluate
#check MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges.edgeCall_of_evaluate

namespace MicroCFTA.PartialRangesIndependentProbes
open Language InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorkerRanges
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

-- Failed observations require no continuation fact.
example (fault : SourceCurrentAllocatedPartialWorker.Fault width) (before : Caller width)
    (next : Node → Caller width → Prop) : After (.failed fault before) next := True.intro

-- A ready node needs no body range plan, including at zero outer fuel.
example (g s r e p h m c n budget : Nat) (request : NodeRequest) (before after : Caller width)
    (handle : Nat) (value : Node) (hit : beginNode request before = (handle, .ready value, after)) :
    nodeCall 0 g s r e p h m c n budget request before := by simp only [nodeCall, hit]

-- Busy is a checked incomplete path, not a successful execution conclusion.
example (fuel g s r e p h m c n budget : Nat) (request : NodeRequest) (before after : Caller width)
    (handle : Nat) (busy : beginNode request before = (handle, .busy, after)) :
    nodeCall fuel g s r e p h m c n budget request before ∧
      SourceCurrentAllocatedPartialWorker.nodeCall fuel g s r e p h m c n budget request before =
        .failed (.nodeMemo handle .busy) after := by
  exact ⟨by simp only [nodeCall, busy],
    SourceCurrentAllocatedPartialWorker.nodeCall_busy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ busy⟩

-- A bare reference imposes no machine range condition while retaining its explicit source error.
example (fuel g s r e p h m c n budget : Nat) (inherited : EqValue)
    (name : InternedBinderProtocol.Reference) (before : Caller width) :
    nodeBody fuel g s r e p h m c n budget ⟨inherited, .reference name⟩ before ∧
      SourceCurrentAllocatedPartialWorker.nodeBody fuel g s r e p h m c n budget ⟨inherited, .reference name⟩ before =
        .failed (.unexpectedReference name) before := by
  exact ⟨by simp only [nodeBody], by simp only [SourceCurrentAllocatedPartialWorker.nodeBody]⟩

-- A failed actual parent does not demand its ResidentRanges plan.
example (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest) (before : Caller width)
    (fault : SourceCurrentAllocatedParentWorker.Fault width) (checked : SourceEqualityNativeDemand.State width)
    (fourth : SourceCurrentEmptinessMemo.Memo) (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
    (failed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget request.value.entry.key.symbol
      request.value.entry.key.constraint request.inherited request.value.children before.checked before.fourth before.merge =
        .failed fault checked fourth memo) : edgeBody fuel g s r e p h m c n budget request before := by
  simp only [edgeBody, failed]

-- Actual successful edge-body execution exposes the exact initial resident range plan.
example {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    (ranges : edgeBody fuel g s r e p h m c n budget request before)
    (done : SourceCurrentAllocatedPartialWorker.edgeBody fuel g s r e p h m c n budget request before = .done result after) :
    SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before := edgeBody_of_done ranges done

-- Ordinary bodies use the exact decremented outer bound and original row list.
example {fuel g s r e p h m c n budget : Nat} {inherited : EqValue} {entry : Cache.Interned InternedBinderProtocol.NodeKey}
    {original : List Edge} {depth : Nat} {free : List InternedBinderProtocol.Reference} {before : Caller width}
    (ranges : nodeBody (fuel + 1) g s r e p h m c n budget ⟨inherited, .node entry original depth free⟩ before) :
    rows fuel g s r e p h m c n budget inherited original before := by simpa only [nodeBody] using ranges

-- Row suffix checks use the exact parent and descendant returns, without an arbitrary future state.
example {fuel g s r e p h m c n budget : Nat} {inherited : EqValue} {original narrowed result : Edge}
    {rest : List Edge} {before middle after : Caller width}
    (ranges : rows (fuel + 1) g s r e p h m c n budget inherited (original :: rest) before)
    (head : SourceCurrentAllocatedPartialWorker.edgeCall fuel g s r e p h m c n budget ⟨inherited, original⟩ before = .done narrowed middle)
    (child : SourceCurrentAllocatedPartialWorker.descendants fuel g s r e p h m c n budget inherited narrowed middle = .done result after) :
    edgeCall fuel g s r e p h m c n budget ⟨inherited, original⟩ before ∧
      descendants fuel g s r e p h m c n budget inherited narrowed middle ∧
      rows fuel g s r e p h m c n budget inherited rest after := by
  have actual := ranges
  simp only [rows] at actual
  have next := after_of_done (value := narrowed) (after := middle) actual.2 head
  exact ⟨actual.1, next.1, after_of_done (value := result) (after := after) next.2 child⟩

-- Failed parent calls skip every descendant and suffix check after the current call's check.
example {fuel g s r e p h m c n budget : Nat} {inherited : EqValue} {original : Edge} {rest : List Edge}
    {before after : Caller width} {fault : SourceCurrentAllocatedPartialWorker.Fault width}
    (current : edgeCall fuel g s r e p h m c n budget ⟨inherited, original⟩ before)
    (failed : SourceCurrentAllocatedPartialWorker.edgeCall fuel g s r e p h m c n budget ⟨inherited, original⟩ before = .failed fault after) :
    rows (fuel + 1) g s r e p h m c n budget inherited (original :: rest) before := by
  simpa only [rows, failed, After, and_true] using current

-- An inherited accessor error checks no children.
example {fuel g s r e p h m c n budget : Nat} {inherited : EqValue} {edge : Edge} {before : Caller width} {message : String}
    (failed : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited before.checked.operations).1 = .error message) :
    descendants fuel g s r e p h m c n budget inherited edge before := by simp only [descendants, failed]

-- Successful inherited allocation uses its actual prefix state with the same budget and bounds.
example {fuel g s r e p h m c n budget : Nat} {inherited combined : EqValue} {edge : Edge} {before : Caller width}
    (ranges : descendants fuel g s r e p h m c n budget inherited edge before)
    (prefixDone : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited before.checked.operations).1 = .ok (some combined)) :
    children fuel g s r e p h m c n budget combined edge.children
      (SourceCurrentAllocatedPartialGraph.prefixState before edge inherited) := by
  simpa only [descendants, prefixDone] using ranges

-- Indexed checks select the literal descended payload and next actual caller state.
example {fuel g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat} {value result : Node}
    {rest : List Node} {before middle : Caller width}
    (ranges : walk (fuel + 1) g s r e p h m c n budget combined index (value :: rest) before)
    (head : SourceCurrentAllocatedPartialWorker.nodeCall fuel g s r e p h m c n budget
      ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1, value⟩
      (SourceCurrentAllocatedPartialGraph.descend before combined index).2 = .done result middle) :
    nodeCall fuel g s r e p h m c n budget
      ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1, value⟩
      (SourceCurrentAllocatedPartialGraph.descend before combined index).2 ∧
      walk fuel g s r e p h m c n budget combined (index + 1) rest middle := by
  have actual := ranges
  simp only [walk] at actual
  exact ⟨actual.1, after_of_done (value := result) (after := middle) actual.2 head⟩

-- Contradiction checks no unresolved child and needs no outer or lower bound.
example (budget : Nat) (name : InternedBinderProtocol.Reference) (before : Caller width) :
    children 0 0 0 0 0 0 0 0 0 0 budget .contradiction [.reference name] before := by
  simp only [children]

-- An empty indexed walk has no request or future suffix check.
example (budget : Nat) (combined : EqValue) (index : Nat) (before : Caller width) :
    walk 0 0 0 0 0 0 0 0 0 0 budget combined index [] before := by simp only [walk]
end MicroCFTA.PartialRangesIndependentProbes
