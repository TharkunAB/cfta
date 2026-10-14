import MicroCFTA.SourceRecursiveIntersectionNativeConstructorSite

/-!
# Split actual pending construction through appended code

A constructor block occurs in the original body or after that body returns.
The split retains the exact remaining code, shared state, and finite counts.
No completed body is supplied to obtain this alternative.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Actual appended construction blocks in its body or in its continuation after an actual returned value. -/
theorem constructor_bind_cases [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (key : NodeKey) (remaining : Code Symbol Guard B)
    (blocked : execute emptyGuard conjoin fuel (code.bind next) state = .blocked (.constructor key) remaining after) :
    (∃ inner rest, inner ≤ fuel ∧ execute emptyGuard conjoin inner code state = .blocked (.constructor key) rest after ∧
      remaining = rest.bind next) ∨
    (∃ inner outer value middle, inner + outer ≤ fuel ∧ Steps emptyGuard conjoin inner code state (.pure value) middle ∧
      execute emptyGuard conjoin outer (next value) middle = .blocked (.constructor key) remaining after) := by
  induction fuel generalizing code state with
  | zero => cases blocked
  | succ fuel ih =>
      have boundStep := step_bind emptyGuard conjoin code next state
      cases one : step emptyGuard conjoin code state with
      | done value initial =>
          obtain ⟨pure, retained⟩ := (step_done_iff emptyGuard conjoin code state initial value).mp one
          subst code
          subst initial
          exact Or.inr ⟨0, fuel + 1, value, state, by omega, .refl _ _, blocked⟩
      | yielded body middle =>
          have tail : execute emptyGuard conjoin fuel (body.bind next) middle = .blocked (.constructor key) remaining after := by
            simpa only [execute, boundStep, one, appendStep] using blocked
          rcases ih body middle tail with ⟨inner, rest, smaller, pending, same⟩ | ⟨inner, outer, value, final, smaller, trace, pending⟩
          · exact Or.inl ⟨inner + 1, rest, by omega, by simpa only [execute, one] using pending, same⟩
          · exact Or.inr ⟨inner + 1, outer, value, final, by omega, .cons _ _ _ _ _ _ inner one trace, pending⟩
      | failed failure middle =>
          simp only [execute, boundStep, one, appendStep] at blocked
          cases blocked
      | blocked reason rest middle =>
          have same := Outcome.blocked.inj (by simpa only [execute, boundStep, one, appendStep] using blocked)
          rcases same with ⟨rfl, rfl, rfl⟩
          exact Or.inl ⟨1, rest, by omega, by simp only [execute, one], rfl⟩

end MicroCFTA.SourceRecursiveIntersectionNative
