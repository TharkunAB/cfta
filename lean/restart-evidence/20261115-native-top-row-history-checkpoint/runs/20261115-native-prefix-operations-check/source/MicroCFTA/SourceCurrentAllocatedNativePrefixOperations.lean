import MicroCFTA.SourceCurrentAllocatedNativePrefixInputs
import MicroCFTA.SourceEqualityNativeDemandOperations

/-!
# Operation facts at the same actual native prefix

The original fields plan supplies each reached instruction's field check.
Actual yielded steps preserve valid growing operation caches.
The same prefix retains both bound and raw remaining plans.
No future completion or semantic state invariant is required.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativePrefixOperations
open InternedConstructorTemplates SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionKernel (Extension)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
variable {width : Nat} {A B : Type}

set_option autoImplicit false

private theorem operations_grows_trans
    {before middle after : SourceEqualityConstraintMemoAllocation.State}
    (first : SourceEqualityConstraintMemoAllocation.Grows before middle)
    (second : SourceEqualityConstraintMemoAllocation.Grows middle after) :
    SourceEqualityConstraintMemoAllocation.Grows before after :=
  ⟨SourceEqualityConstraintAllocation.steps_trans first.constraints second.constraints,
    Cache.extends_trans first.combinations second.combinations,
    Cache.extends_trans first.descents second.descents⟩

private theorem fields_through_before_bind
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control A) (next : A → Code Symbol Guard B) (before : Checked width)
    (fields : FieldsThrough fuel (control.bind next) before) :
    FieldsThrough fuel control before := by
  induction fuel generalizing control before with
  | zero => cases control <;> exact fields
  | succ fuel ih =>
      refine ⟨?_, ?_⟩
      · cases control <;> exact fields.1
      · cases one : step control before with
        | yielded rest after =>
            have boundOne := step_bind control next before
            rw [one, appendStep] at boundOne
            have remaining := fields.2
            rw [boundOne] at remaining
            exact ih rest after remaining
        | done | failed | constraintError | blocked => trivial

private theorem prefix_operations_and_fields
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {budget used : Nat} {original remaining : Control B} {before after : Checked width}
    (fields : FieldsThrough budget original before)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (actual : Steps used original before remaining after) (bounded : used ≤ budget) :
    SourceEqualityConstraintMemoAllocation.Valid after.operations ∧
    SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations ∧
    FieldsThrough (budget - used) remaining after := by
  induction actual generalizing budget with
  | refl => exact ⟨valid, SourceEqualityConstraintMemoAllocation.grows_refl _,
      by simpa only [Nat.sub_zero] using fields⟩
  | cons control state next reached final result count one tail ih =>
      cases budget with
      | zero => omega
      | succ budget =>
          have checked := SourceEqualityNativeDemandOperations.step_operations control state valid fields.1
          have current : SourceEqualityConstraintMemoAllocation.Valid reached.operations ∧
              SourceEqualityConstraintMemoAllocation.Grows state.operations reached.operations := by
            simpa only [one, Outcome.state] using checked
          have nextFields : FieldsThrough budget next reached := by
            have remaining := fields.2
            rw [one] at remaining
            exact remaining
          obtain ⟨laterValid, laterGrowth, laterFields⟩ := ih nextFields current.1 (by omega)
          refine ⟨laterValid, operations_grows_trans current.2 laterGrowth, ?_⟩
          have sameBudget : budget + 1 - (count + 1) = budget - count := by omega
          simpa only [sameBudget] using laterFields

/-- A literal bounded prefix derives physical and operation facts at its exact reached state. -/
theorem prefix_operations_before_bind
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (budget used : Nat) (original : Control B) (control : Control A)
    (next : A → Code Symbol Guard B) (before after : Checked width)
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (physical : Physical before.native)
    (plan : InputsThrough budget original before)
    (fields : FieldsThrough budget original before)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (sourceGrowth : InternedConstructorTemplates.Grows sourceHeap before.native.machine.heap)
    (actual : Steps used original before (control.bind next) after)
    (bounded : used ≤ budget) :
    Trace used original before (control.bind next) after ∧
    Physical after.native ∧ Extension before.native.machine after.native.machine ∧
    InternedConstructorTemplates.Grows sourceHeap after.native.machine.heap ∧
    SourceEqualityConstraintMemoAllocation.Valid after.operations ∧
    SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations ∧
    InputsThrough (budget - used) (control.bind next) after ∧
    InputsThrough (budget - used) control after ∧
    FieldsThrough (budget - used) (control.bind next) after ∧
    FieldsThrough (budget - used) control after := by
  have inputs := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
    budget used original control next before after physical plan actual bounded
  have operations := prefix_operations_and_fields fields valid actual bounded
  exact ⟨inputs.1, inputs.2.1, inputs.2.2.1,
    InternedConstructorTemplates.grows_trans sourceGrowth inputs.2.2.1.heap,
    operations.1, operations.2.1, inputs.2.2.2.1, inputs.2.2.2.2,
    operations.2.2, fields_through_before_bind (budget - used) control next after operations.2.2⟩

end MicroCFTA.SourceCurrentAllocatedNativePrefixOperations

#print axioms MicroCFTA.SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
#check MicroCFTA.SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
