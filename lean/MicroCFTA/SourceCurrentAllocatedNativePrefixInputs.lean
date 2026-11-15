import MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback
import MicroCFTA.SourceCurrentNativeEnterCommonOperand

/-!
# Physical inputs at an actual prefix and its unbound call

The original budget plan supplies each actual prefix check.
The same prefix derives current physical validity and remaining inputs.
Removing its captured continuation retains the exact remaining budget.
No complete future trace or worker-cache readiness is required.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativePrefixInputs
open InternedConstructorTemplates SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionKernel (Extension)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
variable {width : Nat} {A B : Type}

set_option autoImplicit false

private theorem through_before_bind
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control A) (next : A → Code Symbol Guard B) (before : Checked width)
    (plan : InputsThrough fuel (control.bind next) before) :
    InputsThrough fuel control before := by
  induction fuel generalizing control before with
  | zero =>
      exact SourceCurrentAllocatedNativeSemanticTraceReadback.inputs_before_bind control next before plan
  | succ fuel ih =>
      refine ⟨SourceCurrentAllocatedNativeSemanticTraceReadback.inputs_before_bind control next before plan.1, ?_⟩
      cases one : step control before with
      | yielded rest after =>
          have boundOne := step_bind control next before
          rw [one, appendStep] at boundOne
          have remaining := plan.2
          rw [boundOne] at remaining
          exact ih rest after remaining
      | done | failed | constraintError | blocked => trivial

private theorem checked_prefix_and_remaining_inputs
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {budget used : Nat} {initial remaining : Control B} {before after : Checked width}
    (plan : InputsThrough budget initial before)
    (actual : Steps used initial before remaining after)
    (bounded : used ≤ budget) :
    Trace used initial before remaining after ∧ InputsThrough (budget - used) remaining after := by
  induction actual generalizing budget with
  | refl => exact ⟨.refl _ _, by simpa only [Nat.sub_zero] using plan⟩
  | cons control state next reached final result count one tail ih =>
      cases budget with
      | zero => omega
      | succ budget =>
          have nextPlan : InputsThrough budget next reached := by
            have remaining := plan.2
            rw [one] at remaining
            exact remaining
          obtain ⟨checkedTail, checkedPlan⟩ := ih nextPlan (by omega)
          refine ⟨.cons control state next reached final result count plan.1 one checkedTail, ?_⟩
          have sameBudget : budget + 1 - (count + 1) = budget - count := by omega
          simpa only [sameBudget] using checkedPlan

/-- An actual bounded prefix derives physicality and both plans at its same remaining budget. -/
theorem prefix_inputs_before_bind
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (budget used : Nat) (initial : Control B) (control : Control A)
    (next : A → Code Symbol Guard B) (before after : Checked width)
    (physical : Physical before.native)
    (plan : InputsThrough budget initial before)
    (actual : Steps used initial before (control.bind next) after)
    (bounded : used ≤ budget) :
    Trace used initial before (control.bind next) after ∧
    Physical after.native ∧ Extension before.native.machine after.native.machine ∧
    InputsThrough (budget - used) (control.bind next) after ∧
    InputsThrough (budget - used) control after := by
  obtain ⟨checkedPrefix, remaining⟩ := checked_prefix_and_remaining_inputs plan actual bounded
  have effects := SourceCurrentNativeEnterCommonOperand.checked_trace_extension checkedPrefix physical
  exact ⟨checkedPrefix, effects.1, effects.2, remaining,
    through_before_bind (budget - used) control next after remaining⟩

end MicroCFTA.SourceCurrentAllocatedNativePrefixInputs
