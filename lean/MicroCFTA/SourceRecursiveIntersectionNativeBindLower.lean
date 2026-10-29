import MicroCFTA.SourceRecursiveIntersectionNativeTrace
import MicroCFTA.InternedStoredPlanBinderDepthLowerAlgebra

namespace MicroCFTA.SourceRecursiveIntersectionNative
open InternedConstructorTemplates SourceRecursiveIntersectionCode
open InternedStoredPlanBinderDepthProgress

/-- Every appended-code endpoint is an inner endpoint or an actual continuation endpoint. -/
theorem execute_bind_state_cases
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    (∃ inner, (execute emptyGuard conjoin fuel (code.bind next) state).state =
      (execute emptyGuard conjoin inner code state).state) ∨
    ∃ inner value current outer,
      execute emptyGuard conjoin inner code state = .done value current ∧
      (execute emptyGuard conjoin fuel (code.bind next) state).state =
        (execute emptyGuard conjoin outer (next value) current).state := by
  induction fuel generalizing code state with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ fuel ih =>
      cases one : step emptyGuard conjoin code state with
      | yielded body after =>
          have bindOne : step emptyGuard conjoin (code.bind next) state = .yielded (body.bind next) after := by
            simp only [step_bind, one, appendStep]
          rcases ih body after with ⟨inner, same⟩ | ⟨inner, value, current, outer, completed, same⟩
          · exact Or.inl ⟨inner + 1, by simpa only [execute, bindOne, one] using same⟩
          · refine Or.inr ⟨inner + 1, value, current, outer, ?_, ?_⟩
            · simpa only [execute, one] using completed
            · simpa only [execute, bindOne] using same
      | failed failure after =>
          have bindOne : step emptyGuard conjoin (code.bind next) state = .failed failure after := by
            simp only [step_bind, one, appendStep]
          exact Or.inl ⟨1, by simp only [execute, bindOne, one, Outcome.state]⟩
      | blocked reason body after =>
          have bindOne : step emptyGuard conjoin (code.bind next) state = .blocked reason (body.bind next) after := by
            simp only [step_bind, one, appendStep]
          exact Or.inl ⟨1, by simp only [execute, bindOne, one, Outcome.state]⟩
      | done value after =>
          obtain ⟨pure, retained⟩ := (step_done_iff emptyGuard conjoin code state after value).mp one
          subst code
          subst after
          exact Or.inr ⟨1, value, state, fuel + 1, rfl, rfl⟩

/-- Bounds for every inner run and every actual returned continuation bound all appended outcomes. -/
theorem execute_bind_lower
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (bound : Nat)
    (first : ∀ inner, Lower state.machine.heap bound
      (execute emptyGuard conjoin inner code state).state.machine.heap)
    (later : ∀ inner value current,
      execute emptyGuard conjoin inner code state = .done value current →
      ∀ outer, Lower current.machine.heap bound
        (execute emptyGuard conjoin outer (next value) current).state.machine.heap) :
    Lower state.machine.heap bound
      (execute emptyGuard conjoin fuel (code.bind next) state).state.machine.heap := by
  rcases execute_bind_state_cases emptyGuard conjoin fuel code next state with
    ⟨inner, same⟩ | ⟨inner, value, current, outer, completed, same⟩
  · rw [same]
    exact first inner
  · have accumulated : Lower state.machine.heap bound current.machine.heap := by
      simpa only [completed, Outcome.state] using first inner
    rw [same]
    exact accumulated.trans (later inner value current completed outer)

end MicroCFTA.SourceRecursiveIntersectionNative
