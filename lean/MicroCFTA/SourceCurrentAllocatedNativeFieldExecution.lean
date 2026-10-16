import MicroCFTA.SourceCurrentAllocatedNativeFieldClosure

/-!
# Allocated fields in finite checked native execution

Initial same-cache field loads and compiled continuations derive field
availability in the actual returned operation cache and constructor heap.
The native input plan retains its word bounds and actual completion receipts.
No future field invariant is supplied.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeFieldExecution
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionKernel (Extension)
open SourceEqualityNativeDemand
local notation "Heap" => SourceCurrentConjunctionEquality.Fields
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceEqualityNativeDemandValidity (StateValid)
open SourceEqualityNativeDemandFieldExecution (InputsThrough through_fields)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Initial field loads derive reached checks, final loaded fields, and the actual remaining continuation. -/
theorem derive_checks [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (fuel : Nat) (control : Control Output) (state : State width)
    (valid : StateValid holds state) (heap : Heap state.operations state.native.machine.heap) (fields : Fields control state)
    (inputs : InputsThrough holds fuel control state) :
    SourceEqualityNativeDemandValidity.Through holds fuel control state ∧
      SourceCurrentAllocatedNativeFieldClosure.OutcomeFields (execute fuel control state) := by
  induction fuel generalizing control state with
  | zero => exact ⟨⟨inputs, SourceCurrentAllocatedNativeFieldClosure.operation_fields control state heap fields⟩, heap, fields⟩
  | succ fuel ih =>
      have operationFields := SourceCurrentAllocatedNativeFieldClosure.operation_fields control state heap fields
      have one := SourceEqualityNativeDemandValidity.step_invariants holds control state valid inputs.1 operationFields
      have annotations := SourceCurrentAllocatedNativeFieldClosure.step_fields holds control state valid heap inputs.1 fields
      cases observed : step control state with
      | yielded next after =>
          have currentValid : StateValid holds after := by simpa only [observed, Outcome.state] using one.1
          have currentFields : Heap after.operations after.native.machine.heap ∧ Fields next after := by
            simpa only [SourceCurrentAllocatedNativeFieldClosure.OutcomeFields, observed, Outcome.state] using annotations
          have rest := ih next after currentValid currentFields.1 currentFields.2
            (by simpa only [InputsThrough, observed] using inputs.2)
          refine ⟨⟨inputs.1, operationFields, ?_⟩, ?_⟩
          · simpa only [observed] using rest.1
          · simpa only [execute, observed] using rest.2
      | done | failed | constraintError | blocked =>
          refine ⟨⟨inputs.1, operationFields, ?_⟩, ?_⟩
          · simp only [observed]
          · simpa only [execute, observed] using annotations

/-- The initial annotation invariant derives finite checked validity and all actual cache histories. -/
theorem execute_invariants [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (fuel : Nat) (control : Control Output) (state : State width)
    (valid : StateValid holds state) (heap : Heap state.operations state.native.machine.heap) (fields : Fields control state)
    (inputs : InputsThrough holds fuel control state) :
    StateValid holds (execute fuel control state).state ∧
      Extension state.native.machine (execute fuel control state).state.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap (execute fuel control state).state.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations (execute fuel control state).state.operations ∧
      SourceCurrentAllocatedNativeFieldClosure.OutcomeFields (execute fuel control state) ∧
      SourceEqualityNativeDemandOperations.FieldsThrough fuel control state := by
  have derived := derive_checks holds fuel control state valid heap fields inputs
  have checked := SourceEqualityNativeDemandValidity.execute_invariants holds fuel control state valid derived.1
  exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2, derived.2, through_fields holds fuel control state derived.1⟩

end MicroCFTA.SourceCurrentAllocatedNativeFieldExecution
