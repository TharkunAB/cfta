import MicroCFTA.SourcePruningEnumerationNativeQueryPrefixArity
import MicroCFTA.SourcePruningEnumerationNativeOutcomeTrace

/-!
# Arity through every finite native query outcome

The physical plan derives the actual reached prefix and terminal step.
The query prefix theorem checks every record created on that prefix.
The terminal step preserves the same invariant at its actual returned heap.
-/
namespace MicroCFTA.SourcePruningEnumerationNativePrefixArity
open InternedConstructorTemplates SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourcePruningEnumerationArityOrigins (Fits Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem execute_heap_of_prefixes (control : Control A) (before : Checked width) (fuel : Nat)
    (valid : Good before)
    (fields : Fields control before) (plan : InputsThrough fuel control before)
    (prefixes : ∀ used after remaining, Trace used control before remaining after → Heap after.native.machine.heap) :
    Heap (execute fuel control before).state.native.machine.heap := by
  have observed := SourcePruningEnumerationNativeOutcomeTrace.execute_readback fuel control before plan
  cases actual : execute fuel control before with
  | yielded next after =>
      simp only [actual] at observed
      exact prefixes fuel after next observed.1
  | done value after =>
      simp only [actual] at observed
      obtain ⟨used, _bounded, trace⟩ := observed
      exact prefixes used after (.code (.pure value)) trace
  | failed failure after =>
      simp only [actual] at observed
      obtain ⟨used, last, current, _bounded, trace, inputs, one⟩ := observed
      have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects trace valid fields
      have currentHeap := prefixes used current last trace
      have retained := SourcePruningEnumerationNativeOutcomeTrace.terminal_step_heap last current reached.1
        currentHeap inputs (by simpa only [one] using True.intro)
      simpa only [one, Outcome.state] using retained
  | constraintError message after =>
      simp only [actual] at observed
      obtain ⟨used, last, current, _bounded, trace, inputs, one⟩ := observed
      have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects trace valid fields
      have currentHeap := prefixes used current last trace
      have retained := SourcePruningEnumerationNativeOutcomeTrace.terminal_step_heap last current reached.1
        currentHeap inputs (by simpa only [one] using True.intro)
      simpa only [one, Outcome.state] using retained
  | blocked reason next after =>
      simp only [actual] at observed
      obtain ⟨used, last, current, _bounded, trace, inputs, one⟩ := observed
      have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects trace valid fields
      have currentHeap := prefixes used current last trace
      have retained := SourcePruningEnumerationNativeOutcomeTrace.terminal_step_heap last current reached.1
        currentHeap inputs (by simpa only [one] using True.intro)
      simpa only [one, Outcome.state] using retained

/-- Every finite node-query outcome retains arity of all records at its actual output heap. -/
theorem node_query_execute_heap (request : NodeRequest Symbol Guard) (before : Checked width) (fuel : Nat)
    (valid : Good before) (heap : Heap before.native.machine.heap)
    (plan : InputsThrough fuel (.code (requestNode request.domain request.left request.right)) before) :
    Heap (execute fuel (.code (requestNode request.domain request.left request.right)) before).state.native.machine.heap :=
  execute_heap_of_prefixes _ before fuel valid (fun _ => trivial) plan
    (fun used after remaining trace => node_query_prefix_heap request before after remaining used valid heap trace)

/-- Every finite edge-query outcome retains arity, including errors and blocked constructor outcomes. -/
theorem edge_query_execute_heap (request : EdgeRequest Symbol Guard) (before : Checked width) (fuel : Nat)
    (valid : Good before) (heap : Heap before.native.machine.heap)
    (plan : InputsThrough fuel (.code (requestEdge request.domain request.left request.right)) before) :
    Heap (execute fuel (.code (requestEdge request.domain request.left request.right)) before).state.native.machine.heap :=
  execute_heap_of_prefixes _ before fuel valid (fun _ => trivial) plan
    (fun used after remaining trace => edge_query_prefix_heap request before after remaining used valid heap trace)

/-- Completed edge memo cells retain arity after every finite physical node-query outcome. -/
theorem node_execute_edge_memo_fits (request : NodeRequest Symbol Guard)
    (before : Checked width) (fuel : Nat) (valid : Good before) (heap : Heap before.native.machine.heap)
    (plan : InputsThrough fuel (.code (requestNode request.domain request.left request.right)) before)
    (handle : Nat) (original : EdgeRequest Symbol Guard) (edge : EdgeValue Symbol Guard)
    (stored : (execute fuel (.code (requestNode request.domain request.left request.right)) before).state.native.edges.cells handle =
      some ⟨original, .returned edge⟩) : Fits edge.entry.key.constraint edge.children.length := by
  have afterHeap := node_query_execute_heap request before fuel valid heap plan
  have reached := SourceCurrentAllocatedNativePhysicalCompletion.execute_invariants fuel
    (.code (requestNode request.domain request.left request.right)) before valid plan (fun _ => trivial)
  have resident := (reached.1.native.edges.checked handle _ stored).2
  exact afterHeap.edge _ reached.1.heap.semantic.1.normal.facts.coherent edge resident

end MicroCFTA.SourcePruningEnumerationNativePrefixArity
