import MicroCFTA.SourceRecursiveIntersectionNativeTraceSplit

/-!
# Split actual finite prefixes at native continuations

A prefix remains inside a nonreturning inner body or contains a complete
inner body and a prefix of the outer continuation. Exact step counts and
shared caches are retained. A completed body also bounds every other prefix.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- A finite prefix stops inside an inner body or after its exact complete return. -/
theorem steps_bind_cases [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (remaining : Code Symbol Guard B)
    (trace : Steps emptyGuard conjoin fuel (code.bind next) state remaining after) :
    (∃ inner, Steps emptyGuard conjoin fuel code state inner after ∧
      (∀ value, inner ≠ .pure value) ∧ remaining = inner.bind next) ∨
    (∃ inner outer value middle, inner + outer = fuel ∧
      Steps emptyGuard conjoin inner code state (.pure value) middle ∧
      Steps emptyGuard conjoin outer (next value) middle remaining after) := by
  induction fuel generalizing code state with
  | zero =>
      obtain ⟨same, retained⟩ := steps_zero emptyGuard conjoin _ _ _ _ trace
      subst remaining
      subst after
      cases code with
      | pure value => exact Or.inr ⟨0, 0, value, state, rfl, .refl _ _, .refl _ _⟩
      | _ => exact Or.inl ⟨_, .refl _ _, (by intro value impossible; cases impossible), rfl⟩
  | succ fuel ih =>
      obtain ⟨rest, current, oneBound, tail⟩ := steps_succ emptyGuard conjoin fuel _ _ _ _ trace
      have boundStep := step_bind emptyGuard conjoin code next state
      cases one : step emptyGuard conjoin code state with
      | done result initial =>
          obtain ⟨pure, retained⟩ := (step_done_iff emptyGuard conjoin code state initial result).mp one
          subst code
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
      | failed failure middle | blocked reason body middle =>
          rw [one, appendStep] at boundStep
          cases boundStep.symm.trans oneBound

/-- A complete native return bounds every actual yielded prefix of that same call. -/
theorem Steps.length_le_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {steps fuel : Nat}
    {code remaining : Code Symbol Guard A} {state after final : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    {value : A} (complete : Steps emptyGuard conjoin steps code state (.pure value) final)
    (actualPrefix : Steps emptyGuard conjoin fuel code state remaining after) : fuel ≤ steps := by
  induction steps generalizing code state fuel with
  | zero =>
      obtain ⟨same, _⟩ := steps_zero emptyGuard conjoin _ _ _ _ complete
      subst code
      cases actualPrefix with
      | refl => omega
      | cons code state rest current remaining after fuel one tail => cases one
  | succ steps ih =>
      obtain ⟨rest, current, one, tail⟩ := steps_succ emptyGuard conjoin steps _ _ _ _ complete
      cases actualPrefix with
      | refl => omega
      | cons code state other middle remaining after fuel first later =>
          obtain ⟨same, retained⟩ := Outcome.yielded.inj (one.symm.trans first)
          subst other
          subst middle
          have bounded := ih tail later
          omega

end MicroCFTA.SourceRecursiveIntersectionNative
