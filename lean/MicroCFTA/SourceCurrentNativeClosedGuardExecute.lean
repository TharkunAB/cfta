import MicroCFTA.SourceCurrentNativeClosedGuardAlphabet

/-!
# Closed guard alphabets through bounded native execution

Every bounded outcome retains the same closed guard alphabet in its heap.
Physical input checks and initial field premises remain explicit.
-/
namespace MicroCFTA.SourceCurrentNativeClosedGuardAlphabet
open InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Good" => SourceCurrentAllocatedNativePhysicalCompletion.Good
local notation "Allocated" => SourceCurrentAllocatedNativeFieldClosure.Fields
variable {A : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Every bounded outcome retains the same closed guard alphabet in its heap. -/
theorem execute_guard_heap (alphabet : List Guard) (closed : Closed alphabet)
    (fuel : Nat) (control : SourceEqualityNativeDemand.Control A)
    (state : SourceEqualityNativeDemand.State width) (good : Good state)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough fuel control state)
    (allocated : Allocated control state)
    (known : Heap (fun guard => guard ∈ alphabet) state.native.machine.heap)
    (guards : SourceCurrentNativeGuardStep.Fields alphabet control) :
    Heap (fun guard => guard ∈ alphabet)
      (SourceEqualityNativeDemand.execute fuel control state).state.native.machine.heap := by
  induction fuel generalizing control state with
  | zero =>
      simpa only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.Outcome.state] using known
  | succ fuel ih =>
      have retained := SourceCurrentNativeGuardStep.step_heap alphabet control state
        good inputs.1 known guards
      have physical := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants
        control state good inputs.1 allocated
      cases actual : SourceEqualityNativeDemand.step control state with
      | yielded next after =>
          have afterGood : Good after := by
            simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using physical.1
          have afterAllocated : Allocated next after := by
            simpa only [actual] using physical.2.2.2.2.2
          have afterKnown : Heap (fun guard => guard ∈ alphabet) after.native.machine.heap := by
            simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using retained
          have produced := SourceCurrentNativeGuardStep.yielded_fields alphabet control next
            state after good inputs.1 allocated known guards actual
          have afterGuards := SourceCurrentNativeGuardStep.fields_mono
            (step_subset alphabet closed) next produced
          have rest := ih next after afterGood
            (by simpa only [SourceCurrentAllocatedNativePhysicalExecution.InputsThrough, actual] using inputs.2)
            afterAllocated afterKnown afterGuards
          simpa only [SourceEqualityNativeDemand.execute, actual] using rest
      | done | failed | constraintError | blocked =>
          simpa only [SourceEqualityNativeDemand.execute, actual,
            SourceEqualityNativeDemand.Outcome.state] using retained

end MicroCFTA.SourceCurrentNativeClosedGuardAlphabet
