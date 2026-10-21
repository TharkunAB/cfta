import MicroCFTA.SourceEqualityNativeDemandFieldClosure

/-!
# Derived field checks for finite checked execution

The initial physical annotation invariant and compiled continuation facts
derive normalized fields along actual execution. Only native current-input
checks remain explicit. They include word bounds and checked semantic
receipts at the actual original completion cells.
-/
namespace MicroCFTA.SourceEqualityNativeDemandFieldExecution
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionKernel (Extension)
open SourceEqualityNativeDemand
open SourceEqualityNativeDemandFieldHeap (Heap)
open SourceEqualityNativeDemandFieldClosure (Fields)
open SourceEqualityNativeDemandValidity (StateValid)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Native input checks follow only actual reached controls and states. No field check is supplied. -/
noncomputable def InputsThrough [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) : Nat → Control Output → State width → Prop
  | 0, control, state => SourceEqualityNativeDemandValidity.Inputs holds control state
  | fuel + 1, control, state => SourceEqualityNativeDemandValidity.Inputs holds control state ∧
      match step control state with
      | .yielded next after => InputsThrough holds fuel next after
      | .done _ _ | .failed _ _ | .constraintError _ _ | .blocked _ _ _ => True

/-- Actual dynamic field closure derives every normalized-field check and the final physical invariant. -/
theorem derive_checks [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (fuel : Nat) (control : Control Output) (state : State width)
    (valid : StateValid holds state) (heap : Heap state.native.machine.heap) (fields : Fields control state)
    (inputs : InputsThrough holds fuel control state) :
    SourceEqualityNativeDemandValidity.Through holds fuel control state ∧
      Heap (execute fuel control state).state.native.machine.heap := by
  induction fuel generalizing control state with
  | zero => exact ⟨⟨inputs, SourceEqualityNativeDemandFieldClosure.operation_fields control state heap fields⟩, heap⟩
  | succ fuel ih =>
      have operationFields := SourceEqualityNativeDemandFieldClosure.operation_fields control state heap fields
      have one := SourceEqualityNativeDemandValidity.step_invariants holds control state valid inputs.1 operationFields
      have annotations := SourceEqualityNativeDemandFieldClosure.step_fields holds control state valid heap inputs.1 fields
      cases observed : step control state with
      | yielded next after =>
          have currentValid : StateValid holds after := by simpa only [observed, Outcome.state] using one.1
          have currentFields : Heap after.native.machine.heap ∧ Fields next after := by
            simpa only [SourceEqualityNativeDemandFieldClosure.OutcomeFields, observed, Outcome.state] using annotations
          have rest := ih next after currentValid currentFields.1 currentFields.2
            (by simpa only [InputsThrough, observed] using inputs.2)
          refine ⟨⟨inputs.1, operationFields, ?_⟩, ?_⟩
          · simpa only [observed] using rest.1
          · simpa only [execute, observed] using rest.2
      | done | failed | constraintError | blocked =>
          refine ⟨⟨inputs.1, operationFields, ?_⟩, ?_⟩
          · simp only [observed]
          · simpa only [execute, observed, SourceEqualityNativeDemandFieldClosure.OutcomeFields, Outcome.state] using annotations.1

/-- Derived current checks supply the original normalized-field plan at each actual reached control. -/
theorem through_fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (fuel : Nat) (control : Control Output) (state : State width)
    (checks : SourceEqualityNativeDemandValidity.Through holds fuel control state) :
    SourceEqualityNativeDemandOperations.FieldsThrough fuel control state := by
  induction fuel generalizing control state with
  | zero => exact checks.2
  | succ fuel ih =>
      refine ⟨checks.2.1, ?_⟩
      cases observed : step control state with
      | yielded next after => exact ih next after (by simpa only [SourceEqualityNativeDemandValidity.Through, observed] using checks.2.2)
      | done | failed | constraintError | blocked => trivial

/-- The initial annotation invariant derives finite checked validity and all actual cache histories. -/
theorem execute_invariants [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (fuel : Nat) (control : Control Output) (state : State width)
    (valid : StateValid holds state) (heap : Heap state.native.machine.heap) (fields : Fields control state)
    (inputs : InputsThrough holds fuel control state) :
    StateValid holds (execute fuel control state).state ∧
      Extension state.native.machine (execute fuel control state).state.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap (execute fuel control state).state.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations (execute fuel control state).state.operations ∧
      Heap (execute fuel control state).state.native.machine.heap ∧
      SourceEqualityNativeDemandOperations.FieldsThrough fuel control state := by
  have derived := derive_checks holds fuel control state valid heap fields inputs
  have checked := SourceEqualityNativeDemandValidity.execute_invariants holds fuel control state valid derived.1
  exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2, derived.2, through_fields holds fuel control state derived.1⟩

end MicroCFTA.SourceEqualityNativeDemandFieldExecution
