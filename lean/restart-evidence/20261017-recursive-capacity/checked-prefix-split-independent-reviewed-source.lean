import MicroCFTA.SourceEqualityNativeDemandTraceSplit

/-!
# Split actual checked prefixes at source continuations

A raw prefix either remains inside a nonpure inner control or reaches
the exact inner return and continues outside it. The split retains
step counts, both native memo families, and all equality-operation caches.
-/
namespace MicroCFTA.SourceEqualityNativeDemand
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- A raw appended prefix stops inside the body or after its actual return. -/
theorem steps_bind_cases [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control A) (next : A → Code Symbol Guard B)
    (state after : State width) (remaining : Control B)
    (trace : Steps fuel (control.bind next) state remaining after) :
    (∃ inner, Steps fuel control state inner after ∧
      (∀ value, inner ≠ .code (.pure value)) ∧ remaining = inner.bind next) ∨
    (∃ inner outer value middle, inner + outer = fuel ∧
      Steps inner control state (.code (.pure value)) middle ∧
      Steps outer (.code (next value)) middle remaining after) := by
  induction fuel generalizing control state with
  | zero =>
      obtain ⟨same, retained⟩ := steps_zero _ _ _ _ trace
      subst remaining
      subst after
      cases control with
      | edgeBody => exact Or.inl ⟨_, .refl _ _, (by intro value impossible; cases impossible), rfl⟩
      | code code =>
          cases code with
          | pure value => exact Or.inr ⟨0, 0, value, state, rfl, .refl _ _, .refl _ _⟩
          | _ => exact Or.inl ⟨_, .refl _ _, (by intro value impossible; cases impossible), rfl⟩
  | succ fuel ih =>
      obtain ⟨rest, current, oneBound, tail⟩ := steps_succ fuel _ _ _ _ trace
      have boundStep := step_bind control next state
      cases one : step control state with
      | done result initial =>
          obtain ⟨pure, retained⟩ := (step_done_iff control state initial result).mp one
          subst control
          subst initial
          exact Or.inr ⟨0, fuel + 1, result, state, by omega, .refl _ _, trace⟩
      | yielded body middle =>
          rw [one, appendStep] at boundStep
          obtain ⟨same, retained⟩ := Outcome.yielded.inj (boundStep.symm.trans oneBound)
          subst rest
          subst current
          rcases ih body middle tail with ⟨inner, bodyTrace, nonpure, same⟩ |
              ⟨inner, outer, value, final, count, bodyTrace, outerTrace⟩
          · exact Or.inl ⟨inner, .cons _ _ _ _ _ _ fuel one bodyTrace, nonpure, same⟩
          · exact Or.inr ⟨inner + 1, outer, value, final, by omega,
              .cons _ _ _ _ _ _ inner one bodyTrace, outerTrace⟩
      | failed failure middle | constraintError message middle | blocked reason body middle =>
          rw [one, appendStep] at boundStep
          cases boundStep.symm.trans oneBound

/-- A complete checked return bounds every raw yielded prefix of that same call. -/
theorem Steps.length_le_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {steps fuel : Nat} {control remaining : Control A} {state after final : State width}
    {value : A} (complete : Steps steps control state (.code (.pure value)) final)
    (actualPrefix : Steps fuel control state remaining after) : fuel ≤ steps := by
  induction steps generalizing control state fuel with
  | zero =>
      obtain ⟨same, _⟩ := steps_zero _ _ _ _ complete
      subst control
      cases actualPrefix with
      | refl => omega
      | cons control state rest current remaining after fuel one tail => cases one
  | succ steps ih =>
      obtain ⟨rest, current, one, tail⟩ := steps_succ steps _ _ _ _ complete
      cases actualPrefix with
      | refl => omega
      | cons control state other middle remaining after fuel first later =>
          obtain ⟨same, retained⟩ := Outcome.yielded.inj (one.symm.trans first)
          subst other
          subst middle
          have bounded := ih tail later
          omega

end MicroCFTA.SourceEqualityNativeDemand
