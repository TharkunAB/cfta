import MicroCFTA.SourcePruningEnumerationNativeRequestArity
import MicroCFTA.SourceCurrentNativeTracePrefixBind

/-!
# Arity through actual native request prefixes

The prefix may stop inside its body or after its actual return.
Every split keeps the complete intermediate checked state.
Lookup, demand and finish frames retain the constructor heap.
-/
namespace MicroCFTA.SourcePruningEnumerationNativePrefixArity
open InternedConstructorTemplates SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeSemanticTraceReadback
open SourceCurrentNativeTracePrefixBind (bind_prefix_cases)
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem pure_prefix_heap (first : A) (before after : Checked width)
    (remaining : Control A) (fuel : Nat)
    (trace : Trace fuel (.code (.pure first)) before remaining after)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases trace with
  | refl => exact heap
  | cons control state next current final reached count inputs one tail => cases one

private theorem finish_node_prefix_heap (handle : Nat) (first : Value Symbol Guard)
    (before after : Checked width) (remaining : Control (Value Symbol Guard)) (fuel : Nat)
    (trace : Trace fuel (.code (.finishNode handle first (.pure first))) before remaining after)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases trace with
  | refl => exact heap
  | cons control state next current final reached count inputs one tail =>
      cases one
      exact pure_prefix_heap first _ after remaining count tail heap

private theorem finish_edge_prefix_heap (handle : Nat) (first : EdgeValue Symbol Guard)
    (before after : Checked width) (remaining : Control (EdgeValue Symbol Guard)) (fuel : Nat)
    (trace : Trace fuel (.code (.finishEdge handle first (.pure first))) before remaining after)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases trace with
  | refl => exact heap
  | cons control state next current final reached count inputs one tail =>
      cases one
      exact pure_prefix_heap first _ after remaining count tail heap

/-- An actual node-request prefix uses only its shorter actual body prefix or a warm hit. -/
theorem node_request_prefix_heap (request : NodeRequest Symbol Guard)
    (before after : Checked width) (remaining : Control (Value Symbol Guard)) (fuel : Nat)
    (valid : Good before) (heap : Heap before.native.machine.heap)
    (trace : Trace fuel (.code (requestNode request.domain request.left request.right)) before remaining after)
    (bodies : ∀ (count : Nat) (original : NodeRequest Symbol Guard)
      (start final : Checked width) (rest : Control (Value Symbol Guard)), count < fuel →
      Good start → Heap start.native.machine.heap →
      Trace count (.code (compileNode original)) start rest final → Heap final.native.machine.heap) :
    Heap after.native.machine.heap := by
  cases trace with
  | refl => exact heap
  | cons control state next current final reached count inputs one tail =>
      have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants _ before valid inputs (fun _ => trivial)
      have currentGood : Good current := by simpa only [one, Outcome.state] using checked.1
      have unchanged := SourcePruningEnumerationNativeRequestArity.node_step_heap request
        (.pure : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)) before
      rw [show step (.code (.node request .pure)) before = .yielded next current from one, Outcome.state] at unchanged
      have currentHeap : Heap current.native.machine.heap := by rw [unchanged]; exact heap
      cases selected : lookupNode width request before.native with
      | mk selection chosen =>
          cases selection with
          | direct original =>
              simp only [requestNode, step, SourceRecursiveIntersectionNative.step, selected, lift, code_bind_pure] at one
              cases one
              exact bodies count original _ after remaining (Nat.lt_succ_self _) currentGood currentHeap tail
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
                      exact pure_prefix_heap result _ after remaining count tail currentHeap
                  | evaluate original =>
                      simp only [requestNode, step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                      cases one
                      rcases bind_prefix_cases count (.code (compileNode original))
                          (fun result => .finishNode handle result (.pure result)) _ after remaining tail with
                        ⟨inner, body, _nonpure, _same⟩ | ⟨inner, outer, result, middle, total, body, finish⟩
                      · exact bodies count original _ after inner (Nat.lt_succ_self _) currentGood currentHeap body
                      · have bodyHeap := bodies inner original _ middle (.code (.pure result)) (by omega) currentGood currentHeap body
                        exact finish_node_prefix_heap handle result middle after remaining outer finish bodyHeap

/-- An actual edge-request prefix retains the heap before, inside or after its checked body. -/
theorem edge_request_prefix_heap (request : EdgeRequest Symbol Guard)
    (before after : Checked width) (remaining : Control (EdgeValue Symbol Guard)) (fuel : Nat)
    (valid : Good before) (heap : Heap before.native.machine.heap)
    (trace : Trace fuel (.code (requestEdge request.domain request.left request.right)) before remaining after)
    (bodies : ∀ (count : Nat) (original : EdgeRequest Symbol Guard)
      (start final : Checked width) (rest : Control (EdgeValue Symbol Guard)), count < fuel →
      Good start → EdgeReady start.native.machine original → Heap start.native.machine.heap →
      Trace count (.edgeBody original .pure) start rest final → Heap final.native.machine.heap) :
    Heap after.native.machine.heap := by
  cases trace with
  | refl => exact heap
  | cons control state next current final reached count inputs one tail =>
      have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants _ before valid inputs (fun _ => trivial)
      have currentGood : Good current := by simpa only [one, Outcome.state] using checked.1
      have currentFields := checked.2.2.2.2.2
      rw [one] at currentFields
      have unchanged := SourceEqualityNativeDemandHeap.step_edge_heap request
        (.pure : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard)) before
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
                  exact pure_prefix_heap result _ after remaining count tail currentHeap
              | evaluate original =>
                  simp only [requestEdge, step, selected, demanded] at one
                  cases one
                  rcases bind_prefix_cases count (.edgeBody original .pure)
                      (fun result => .finishEdge handle result (.pure result)) _ after remaining tail with
                    ⟨inner, body, _nonpure, _same⟩ | ⟨inner, outer, result, middle, total, body, finish⟩
                  · exact bodies count original _ after inner (Nat.lt_succ_self _) currentGood currentFields.1 currentHeap body
                  · have bodyHeap := bodies inner original _ middle (.code (.pure result)) (by omega)
                      currentGood currentFields.1 currentHeap body
                    exact finish_edge_prefix_heap handle result middle after remaining outer finish bodyHeap

end MicroCFTA.SourcePruningEnumerationNativePrefixArity
