import MicroCFTA.SourceCurrentConstrainedCapGuardNative
import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion

/-!
# Causal guard heaps through actual checked native prefixes

Current physical work inputs restrict writes to the source constructors.
Actual optional binders retain the guard heap at every stopping outcome.
Memo publication and checked edge bodies retain the same constructor heap.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeGuardHeap
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentConstrainedCapGuardHeap (Heap)
open SourceEqualityRequiredCache (Ready)
open SourceEqualityNativeDemandHeapPrimitives (WorkInputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {width : Nat}

/-- Physical primitive inputs admit only writes that retain existing recursive records. -/
theorem work_heap [DecidableEq (EdgeKey OtherSymbol OtherGuard)] (annotation : OtherGuard → Prop)
    (job : Work OtherSymbol OtherGuard A) (state : InternedConstructorTemplates.State OtherSymbol OtherGuard)
    (inputs : WorkInputs state job) (heap : Heap annotation state) : Heap annotation (run job state).2 := by
  cases inputs with
  | pure => exact heap
  | edge => exact heap
  | node edges resident =>
      exact SourceCurrentConstrainedCapGuardHeap.preserve annotation state _ heap
        (InternedShallowHeap.makeNode_noNewMu edges state)
  | union values available =>
      exact SourceCurrentConstrainedCapGuardHeap.preserve annotation state _ heap
        (InternedShallowHeap.makeUnion_noNewMu values state)

private theorem lift_heap (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard Output) :
    (lift operations outcome).state.native.machine.heap = outcome.state.machine.heap := by
  cases outcome <;> rfl

/-- One actual instruction retains the produced guard heap on every observation. -/
theorem step_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (control : Control Output) (state : State width)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap state.native.machine.heap)
    (inputs : SourceEqualityNativeDemandHeap.Inputs control state)
    (heap : Heap annotation state.native.machine.heap) :
    Heap annotation (step control state).state.native.machine.heap := by
  cases control with
  | edgeBody request next =>
      rw [step, SourceEqualityNativeDemandOperations.body_native]
      exact heap
  | code code =>
      cases code with
      | pure | fail | enter | read | finishNode | finishEdge => exact heap
      | work job next =>
          change Heap annotation
            (lift state.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.work job next) state.native)).state.native.machine.heap
          rw [lift_heap]
          exact work_heap annotation job state.native.machine.heap inputs heap
      | optionalBinder pair body next =>
          have retained := SourceCurrentConstrainedCapGuardNative.optional_heap annotation pair body
            state.native.machine.heap semantic inputs heap
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.native.machine.heap with
          | done value after | pending key after =>
              simpa only [step, SourceRecursiveIntersectionNative.step, actual, lift, Outcome.state,
                SourceRecursiveIntersectionThunks.advance, InternedNestedConstruction.Outcome.state] using retained
      | node request next =>
          change Heap annotation
            (lift state.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.node request next) state.native)).state.native.machine.heap
          rw [lift_heap, SourceRecursiveIntersectionNative.node_step_machine]
          exact heap
      | edge request next =>
          rw [SourceEqualityNativeDemandHeap.step_edge_heap]
          exact heap

/-- Actual finite checked execution retains guard observations without a completion premise. -/
theorem execute_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (fuel : Nat) (control : Control Output) (state : State width)
    (ready : Ready state.native.machine.heap)
    (inputs : SourceEqualityNativeDemandHeap.InputsThrough fuel control state)
    (heap : Heap annotation state.native.machine.heap) :
    Heap annotation (SourceEqualityNativeDemand.execute fuel control state).state.native.machine.heap := by
  induction fuel generalizing control state with
  | zero => exact heap
  | succ fuel ih =>
      have kept := SourceEqualityNativeDemandHeap.step_keeps control state ready inputs.1
      have retained := step_heap annotation control state ready.semantic inputs.1 heap
      cases actual : step control state with
      | yielded next after =>
          have afterReady : Ready after.native.machine.heap := by simpa only [actual, Outcome.state] using kept.ready
          have afterHeap : Heap annotation after.native.machine.heap := by simpa only [actual, Outcome.state] using retained
          have nextInputs : SourceEqualityNativeDemandHeap.InputsThrough fuel next after := by
            simpa only [actual] using inputs.2
          simpa only [SourceEqualityNativeDemand.execute, actual] using ih next after afterReady nextInputs afterHeap
      | done | failed | constraintError | blocked => simpa only [SourceEqualityNativeDemand.execute, actual, Outcome.state] using retained

private theorem physical_inputs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control Output) (state : State width)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs control state) :
    SourceEqualityNativeDemandHeap.Inputs control state := by
  cases control with
  | edgeBody => trivial
  | code code =>
      cases code <;> first | exact inputs | trivial

/-- The same actual physical prefix retains both readiness and its causal guard heap. -/
theorem trace_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {fuel : Nat} {control remaining : Control Output} {before after : State width}
    (trace : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel control before remaining after)
    (ready : Ready before.native.machine.heap) (heap : Heap annotation before.native.machine.heap) :
    Ready after.native.machine.heap ∧ Heap annotation after.native.machine.heap := by
  induction trace with
  | refl => exact ⟨ready, heap⟩
  | cons control state next middle final result fuel inputs actual rest ih =>
      have admitted := physical_inputs control state inputs
      have kept := SourceEqualityNativeDemandHeap.step_keeps control state ready admitted
      have retained := step_heap annotation control state ready.semantic admitted heap
      have middleReady : Ready middle.native.machine.heap := by simpa only [actual, Outcome.state] using kept.ready
      have middleHeap : Heap annotation middle.native.machine.heap := by simpa only [actual, Outcome.state] using retained
      exact ih middleReady middleHeap

end MicroCFTA.SourceCurrentConstrainedCapNativeGuardHeap
