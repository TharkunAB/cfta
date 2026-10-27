import MicroCFTA.SourcePruningEnumerationArityOrigins
import MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback

/-!
# Arity through actual native request frames

Lookup, demand and publication retain the constructor heap.
Completed requests expose their actual shorter body traces.
The body condition applies only to these actual executions.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeRequestArity
open InternedConstructorTemplates SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeSemanticTraceReadback
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem lift_heap (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard A) :
    (lift operations outcome).state.native.machine.heap = outcome.state.machine.heap := by
  cases outcome <;> rfl

/-- Actual node lookup and demand do not change any constructor record. -/
theorem node_step_heap (request : NodeRequest Symbol Guard)
    (next : Value Symbol Guard → Code Symbol Guard A) (state : Checked width) :
    (step (.code (.node request next)) state).state.native.machine.heap = state.native.machine.heap := by
  change (lift state.operations (SourceRecursiveIntersectionNative.step
    SourceEqualityConstraintConstructors.top SourceEqualityPCSNativeEdge.conjoin
    (.node request next) state.native)).state.native.machine.heap = _
  rw [lift_heap, SourceRecursiveIntersectionNative.node_step_machine]

private theorem pure_after_step_heap (control : Control A) (before middle after : Checked width)
    (first value : A) (fuel : Nat)
    (one : step control before = .yielded (.code (.pure first)) middle)
    (same : middle.native.machine.heap = before.native.machine.heap)
    (trace : Trace fuel control before (.code (.pure value)) after)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  obtain ⟨rest, _count, tail⟩ := after_step fuel control _ before middle after value trace one
  obtain ⟨_zero, _value, retained⟩ := pure_trace rest first value middle after tail.steps
  rw [← retained, same]
  exact heap

private theorem finish_node_heap (handle : Nat) (first value : Value Symbol Guard)
    (before after : Checked width) (fuel : Nat)
    (trace : Trace fuel (.code (.finishNode handle first (.pure first))) before (.code (.pure value)) after)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  exact pure_after_step_heap _ before _ after first value fuel rfl rfl trace heap

private theorem finish_edge_heap (handle : Nat) (first value : EdgeValue Symbol Guard)
    (before after : Checked width) (fuel : Nat)
    (trace : Trace fuel (.code (.finishEdge handle first (.pure first))) before (.code (.pure value)) after)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  exact pure_after_step_heap _ before _ after first value fuel rfl rfl trace heap

/-- A completed node request consumes only an actual shorter compiled body or a warm hit. -/
theorem node_request_heap (request : NodeRequest Symbol Guard)
    (before after : Checked width) (value : Value Symbol Guard) (fuel : Nat)
    (valid : Good before) (heap : Heap before.native.machine.heap)
    (trace : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after)
    (bodies : ∀ (count : Nat) (original : NodeRequest Symbol Guard)
      (start final : Checked width) (result : Value Symbol Guard), count < fuel →
      Good start → Heap start.native.machine.heap →
      Trace count (.code (compileNode original)) start (.code (.pure result)) final →
      Heap final.native.machine.heap) : Heap after.native.machine.heap := by
  cases trace with
  | cons control state next current final reached count inputs one tail =>
      have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants _ before valid inputs (fun _ => trivial)
      have currentGood : Good current := by simpa only [one, Outcome.state] using checked.1
      have unchanged := node_step_heap request (.pure : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)) before
      rw [show step (.code (.node request .pure)) before = .yielded next current from one, Outcome.state] at unchanged
      have currentHeap : Heap current.native.machine.heap := by rw [unchanged]; exact heap
      cases selected : lookupNode width request before.native with
      | mk selection chosen =>
          cases selection with
          | direct original =>
              simp only [requestNode, step, SourceRecursiveIntersectionNative.step, selected, lift, code_bind_pure] at one
              cases one
              exact bodies count original _ after value (Nat.lt_succ_self _) currentGood currentHeap tail
          | memoized handle =>
              cases demanded : demandNode handle chosen with
              | mk observation running =>
                  cases observation with
                  | absent | busy =>
                      simp only [requestNode, step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                      cases one
                  | ready result =>
                      simp only [requestNode, step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                      cases one
                      obtain ⟨_zero, _same, retained⟩ := pure_trace count result value _ after tail.steps
                      rw [← retained]
                      exact currentHeap
                  | evaluate original =>
                      simp only [requestNode, step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                      cases one
                      obtain ⟨inner, outer, result, middle, total, body, finish⟩ :=
                        bind_inverse count (.code (compileNode original))
                          (fun result => .finishNode handle result (.pure result)) _ after value tail
                      have bodyHeap := bodies inner original _ middle result (by omega) currentGood currentHeap body
                      exact finish_node_heap handle result value middle after outer finish bodyHeap

/-- A completed edge request consumes only its actual shorter checked body or a warm hit. -/
theorem edge_request_heap (request : EdgeRequest Symbol Guard)
    (before after : Checked width) (value : EdgeValue Symbol Guard) (fuel : Nat)
    (valid : Good before) (heap : Heap before.native.machine.heap)
    (trace : Trace fuel (.code (requestEdge request.domain request.left request.right)) before (.code (.pure value)) after)
    (bodies : ∀ (count : Nat) (original : EdgeRequest Symbol Guard)
      (start final : Checked width) (result : EdgeValue Symbol Guard), count < fuel →
      Good start → EdgeReady start.native.machine original → Heap start.native.machine.heap →
      Trace count (.edgeBody original .pure) start (.code (.pure result)) final →
      Heap final.native.machine.heap) : Heap after.native.machine.heap := by
  cases trace with
  | cons control state next current final reached count inputs one tail =>
      have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants _ before valid inputs (fun _ => trivial)
      have currentGood : Good current := by simpa only [one, Outcome.state] using checked.1
      have currentFields := checked.2.2.2.2.2
      rw [one] at currentFields
      have unchanged := SourceEqualityNativeDemandHeap.step_edge_heap request (.pure : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard)) before
      rw [show step (.code (.edge request .pure)) before = .yielded next current from one, Outcome.state] at unchanged
      have currentHeap : Heap current.native.machine.heap := by rw [unchanged]; exact heap
      cases selected : lookupEdge width request before.native with
      | mk handle chosen =>
          cases demanded : demandEdge handle chosen with
          | mk observation running =>
              cases observation with
              | absent | busy =>
                  simp only [requestEdge, step, selected, demanded] at one
                  cases one
              | ready result =>
                  simp only [requestEdge, step, selected, demanded] at one
                  cases one
                  obtain ⟨_zero, _same, retained⟩ := pure_trace count result value _ after tail.steps
                  rw [← retained]
                  exact currentHeap
              | evaluate original =>
                  simp only [requestEdge, step, selected, demanded] at one
                  cases one
                  obtain ⟨inner, outer, result, middle, total, body, finish⟩ :=
                    bind_inverse count (.edgeBody original .pure)
                      (fun result => .finishEdge handle result (.pure result)) _ after value tail
                  have bodyHeap := bodies inner original _ middle result (by omega) currentGood currentFields.1 currentHeap body
                  exact finish_edge_heap handle result value middle after outer finish bodyHeap

end MicroCFTA.SourcePruningEnumerationNativeRequestArity
