import MicroCFTA.SourceCurrentAllocatedPartialState
import MicroCFTA.SourcePruningEnumerationNativeExecutionArity

/-!
# Arity through actual caller-table updates

Caller publication and completion retain the whole checked state.
Advancement after a native query uses that query's actual returned state.
The query theorem supplies arity for every finite outcome.
-/
namespace MicroCFTA.SourcePruningEnumerationCallerArity
open InternedConstructorTemplates
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
variable {width : Nat}

/-- Node publication and demand retain arity at the exact returned caller. -/
theorem beginNode_heap (request : SourceCurrentAllocatedPartialState.NodeRequest)
    (before : Caller width) (heap : Heap before.checked.native.machine.heap) :
    Heap (SourceCurrentAllocatedPartialState.beginNode request before).2.2.checked.native.machine.heap :=
  heap

/-- Edge publication and demand change no constructor record. -/
theorem beginEdge_heap (request : SourceCurrentAllocatedPartialState.EdgeRequest)
    (before : Caller width) (heap : Heap before.checked.native.machine.heap) :
    Heap (SourceCurrentAllocatedPartialState.beginEdge request before).2.2.checked.native.machine.heap :=
  heap

/-- Node completion retains arity without replacing any other caller field. -/
theorem finishNode_heap (handle : Nat) (result : Node) (before : Caller width)
    (heap : Heap before.checked.native.machine.heap) :
    Heap (SourceCurrentAllocatedPartialState.finishNode handle result before).checked.native.machine.heap :=
  heap

/-- Edge completion retains arity at its actual returned caller. -/
theorem finishEdge_heap (handle : Nat) (result : Edge) (before : Caller width)
    (heap : Heap before.checked.native.machine.heap) :
    Heap (SourceCurrentAllocatedPartialState.finishEdge handle result before).checked.native.machine.heap :=
  heap

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Advancing a caller with an actual node query retains arity for every finite outcome. -/
theorem advance_node_execute_heap
    (request : SourceRecursiveIntersectionThunks.NodeRequest Symbol Guard)
    (before : Caller width) (fuel : Nat)
    (fourth : SourceCurrentEmptinessMemo.Memo)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCompletion.Good before.checked)
    (heap : Heap before.checked.native.machine.heap)
    (plan : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough fuel
      (.code (SourceRecursiveIntersectionCode.requestNode request.domain request.left request.right)) before.checked) :
    Heap (SourceCurrentAllocatedPartialState.advance before
      (SourceEqualityNativeDemand.execute fuel
        (.code (SourceRecursiveIntersectionCode.requestNode request.domain request.left request.right)) before.checked).state
      fourth merge).checked.native.machine.heap :=
  SourcePruningEnumerationNativePrefixArity.node_query_execute_heap request before.checked fuel valid heap plan

/-- Edge-query advancement keeps the literal reached checked state on success or failure. -/
theorem advance_edge_execute_heap
    (request : SourceRecursiveIntersectionThunks.EdgeRequest Symbol Guard)
    (before : Caller width) (fuel : Nat)
    (fourth : SourceCurrentEmptinessMemo.Memo)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCompletion.Good before.checked)
    (heap : Heap before.checked.native.machine.heap)
    (plan : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough fuel
      (.code (SourceRecursiveIntersectionCode.requestEdge request.domain request.left request.right)) before.checked) :
    Heap (SourceCurrentAllocatedPartialState.advance before
      (SourceEqualityNativeDemand.execute fuel
        (.code (SourceRecursiveIntersectionCode.requestEdge request.domain request.left request.right)) before.checked).state
      fourth merge).checked.native.machine.heap :=
  SourcePruningEnumerationNativePrefixArity.edge_query_execute_heap request before.checked fuel valid heap plan

end MicroCFTA.SourcePruningEnumerationCallerArity
