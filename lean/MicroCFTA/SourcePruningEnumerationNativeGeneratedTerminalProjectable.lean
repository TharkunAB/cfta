import MicroCFTA.SourcePruningEnumerationNativeGeneratedProjectable

/-!
# Projectable guards at actual generated native outcomes

Generated query prefixes retain support for the current edge records.
A terminal instruction retains that support at its exact observed state.
Pending optional binding copies guards from the current supported heap.
The public results cover only generated requests and checked bodies.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeGeneratedTerminalProjectable
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
  (fun guard : Guard => ∃ classes, SourceCompactGuards.sourceEqualities guard = some classes)
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
local notation "InputsThrough" => SourceCurrentAllocatedNativePhysicalExecution.InputsThrough
variable {A : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A non-yielding step preserves support; unchecked work cannot be such a step. -/
private theorem terminal_step_heap (control : Control A) (before : Checked width)
    (initial : Good before) (inputs : Inputs control before) (current : Heap before.native.machine.heap)
    (terminal : match SourceEqualityNativeDemand.step control before with
      | .yielded _ _ => False
      | _ => True) :
    Heap (SourceEqualityNativeDemand.step control before).state.native.machine.heap := by
  cases control with
  | edgeBody request next =>
      change Heap (SourceEqualityNativeDemand.body request next before).state.native.machine.heap
      rw [SourceEqualityNativeDemandOperations.body_native]
      exact current
  | code code =>
      cases code with
      | pure | fail => exact current
      | work | enter | read | finishNode | finishEdge => exact False.elim terminal
      | node request next =>
          rw [SourcePruningEnumerationNativeRequestArity.node_step_heap]
          exact current
      | edge request next =>
          rw [SourceEqualityNativeDemandHeap.step_edge_heap]
          exact current
      | optionalBinder key body next =>
          have retained := SourceEqualityAnnotationStoredSyntax.optionalBinder _ key body
            before.native.machine.heap current initial.native.machine.1 inputs
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu key body before.native.machine.heap with
          | done value after =>
              simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
                actual, SourceEqualityNativeDemand.lift, SourceEqualityNativeDemand.Outcome.state,
                advance, InternedNestedConstruction.Outcome.state] using retained
          | pending pending after =>
              simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
                actual, SourceEqualityNativeDemand.lift, SourceEqualityNativeDemand.Outcome.state,
                advance, InternedNestedConstruction.Outcome.state] using retained

/-- Actual generated prefix preservation extends through the observed final instruction. -/
private theorem execute_heap_from_prefixes (fuel : Nat) (control : Control A) (before : Checked width)
    (initial : Good before) (fields : Fields control before) (current : Heap before.native.machine.heap)
    (inputs : InputsThrough fuel control before)
    (prefixes : ∀ (count : Nat), count ≤ fuel → ∀ (remaining : Control A) (after : Checked width),
      Trace count control before remaining after → Heap after.native.machine.heap) :
    Heap (SourceEqualityNativeDemand.execute fuel control before).state.native.machine.heap := by
  induction fuel generalizing control before with
  | zero => exact current
  | succ fuel ih =>
      cases one : SourceEqualityNativeDemand.step control before with
      | yielded next reached =>
          have first : Trace 1 control before next reached :=
            .cons _ _ _ _ _ _ 0 inputs.1 one (.refl _ _)
          have reachedHeap := prefixes 1 (by omega) next reached first
          have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants
            control before initial inputs.1 fields
          rw [one] at checked
          have restInputs : InputsThrough fuel next reached := by
            simpa only [SourceCurrentAllocatedNativePhysicalExecution.InputsThrough, one] using inputs.2
          rw [SourceEqualityNativeDemand.execute, one]
          apply ih next reached checked.1 checked.2.2.2.2.2 reachedHeap restInputs
          intro count bounded remaining after trace
          exact prefixes (count + 1) (by omega) remaining after
            (.cons _ _ _ _ _ _ count inputs.1 one trace)
      | done | failed | constraintError | blocked =>
          have terminal : match SourceEqualityNativeDemand.step control before with
              | .yielded _ _ => False
              | _ => True := by simp only [one]
          have retained := terminal_step_heap control before initial inputs.1 current terminal
          simpa only [SourceEqualityNativeDemand.execute, one, SourceEqualityNativeDemand.Outcome.state]
            using retained

/-- Every observed generated node-query outcome retains support at its exact native state. -/
theorem node_query_outcome_projectable (request : NodeRequest Symbol Guard)
    (before : Checked width) (fuel : Nat)
    (observed : SourceEqualityNativeDemand.Outcome width (Value Symbol Guard))
    (initial : Good before) (current : Heap before.native.machine.heap)
    (inputs : InputsThrough fuel (.code (requestNode request.domain request.left request.right)) before)
    (actual : SourceEqualityNativeDemand.execute fuel
      (.code (requestNode request.domain request.left request.right)) before = observed) :
    Heap observed.state.native.machine.heap := by
  rw [← actual]
  apply execute_heap_from_prefixes fuel
    (.code (requestNode request.domain request.left request.right)) before initial (fun _ => trivial) current inputs
  intro count _bounded remaining after trace
  exact SourcePruningEnumerationNativeGeneratedProjectable.node_query_prefix_projectable
    request before after remaining count initial current trace

/-- Every observed generated edge-query outcome retains support, including blocked and error states. -/
theorem edge_query_outcome_projectable (request : EdgeRequest Symbol Guard)
    (before : Checked width) (fuel : Nat)
    (observed : SourceEqualityNativeDemand.Outcome width (EdgeValue Symbol Guard))
    (initial : Good before) (current : Heap before.native.machine.heap)
    (inputs : InputsThrough fuel (.code (requestEdge request.domain request.left request.right)) before)
    (actual : SourceEqualityNativeDemand.execute fuel
      (.code (requestEdge request.domain request.left request.right)) before = observed) :
    Heap observed.state.native.machine.heap := by
  rw [← actual]
  apply execute_heap_from_prefixes fuel
    (.code (requestEdge request.domain request.left request.right)) before initial (fun _ => trivial) current inputs
  intro count _bounded remaining after trace
  exact SourcePruningEnumerationNativeGeneratedProjectable.edge_query_prefix_projectable
    request before after remaining count initial current trace

/-- Every observed checked-body outcome retains support at its exact returned or stopping state. -/
theorem body_outcome_projectable (request : EdgeRequest Symbol Guard)
    (before : Checked width) (fuel : Nat)
    (observed : SourceEqualityNativeDemand.Outcome width (EdgeValue Symbol Guard))
    (initial : Good before) (operands : EdgeReady before.native.machine request)
    (current : Heap before.native.machine.heap)
    (inputs : InputsThrough fuel (.edgeBody request .pure) before)
    (actual : SourceEqualityNativeDemand.execute fuel (.edgeBody request .pure) before = observed) :
    Heap observed.state.native.machine.heap := by
  rw [← actual]
  apply execute_heap_from_prefixes fuel (.edgeBody request .pure) before initial
    ⟨operands, fun _ => trivial⟩ current inputs
  intro count _bounded remaining after trace
  exact SourcePruningEnumerationNativeGeneratedProjectable.body_prefix_projectable
    request before after remaining count initial operands current trace

end MicroCFTA.SourcePruningEnumerationNativeGeneratedTerminalProjectable
