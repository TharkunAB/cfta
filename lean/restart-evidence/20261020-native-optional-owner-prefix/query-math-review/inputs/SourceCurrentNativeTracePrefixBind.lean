import MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback

/-!
# Physically checked prefixes of appended native code

The actual trace either stays inside the unbound call or reaches its
exact return and continues at the same checked state. Pure returns add
no instruction. Each derived trace retains the actual physical checks.
-/
namespace MicroCFTA.SourceCurrentNativeTracePrefixBind
open InternedConstructorTemplates SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (inputs_before_bind)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {A B : Type} {width : Nat}

/-- An actual bound prefix retains its unfinished call or its exact return and continuation. -/
theorem bind_prefix_cases [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control A) (next : A → Code Symbol Guard B)
    (before after : Checked width) (remaining : Control B)
    (actual : Trace fuel (control.bind next) before remaining after) :
    (∃ inner, Trace fuel control before inner after ∧
      (∀ value, inner ≠ .code (.pure value)) ∧ remaining = inner.bind next) ∨
    (∃ innerFuel outerFuel value middle, innerFuel + outerFuel = fuel ∧
      Trace innerFuel control before (.code (.pure value)) middle ∧
      Trace outerFuel (.code (next value)) middle remaining after) := by
  induction fuel generalizing control before with
  | zero =>
      obtain ⟨same, retained⟩ := steps_zero _ _ _ _ actual.steps
      subst remaining
      subst after
      cases control with
      | edgeBody =>
          exact Or.inl ⟨_, .refl _ _, (by intro value impossible; cases impossible), rfl⟩
      | code code =>
          cases code with
          | pure value => exact Or.inr ⟨0, 0, value, before, rfl, .refl _ _, .refl _ _⟩
          | _ => exact Or.inl ⟨_, .refl _ _, (by intro value impossible; cases impossible), rfl⟩
  | succ fuel ih =>
      cases actual with
      | cons start initial rest current final result count inputs oneBound tail =>
          have boundStep := step_bind control next before
          cases one : step control before with
          | done value initial =>
              obtain ⟨pure, retained⟩ := (step_done_iff control before initial value).mp one
              subst control
              subst initial
              exact Or.inr ⟨0, fuel + 1, value, before, by omega, .refl _ _,
                .cons _ _ _ _ _ _ _ inputs oneBound tail⟩
          | yielded body middle =>
              rw [one, appendStep] at boundStep
              obtain ⟨same, retained⟩ := Outcome.yielded.inj (boundStep.symm.trans oneBound)
              subst rest
              subst current
              rcases ih body middle tail with ⟨inner, bodyTrace, nonpure, same⟩ |
                  ⟨innerFuel, outerFuel, value, final, count, bodyTrace, outerTrace⟩
              · exact Or.inl ⟨inner,
                  .cons _ _ _ _ _ _ _ (inputs_before_bind control next before inputs) one bodyTrace,
                  nonpure, same⟩
              · exact Or.inr ⟨innerFuel + 1, outerFuel, value, final, by omega,
                  .cons _ _ _ _ _ _ _ (inputs_before_bind control next before inputs) one bodyTrace,
                  outerTrace⟩
          | failed failure middle | constraintError message middle | blocked reason body middle =>
              rw [one, appendStep] at boundStep
              cases boundStep.symm.trans oneBound

end MicroCFTA.SourceCurrentNativeTracePrefixBind
