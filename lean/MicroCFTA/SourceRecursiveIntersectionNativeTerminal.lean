import MicroCFTA.SourceRecursiveIntersectionNativeRangeCertificate

/-!
# Exact terminal native observations through continuations

Finite successful results, source failures, and pending constructor keys
remain distinct. Appended code retains the exact failure or blocked
constructor continuation and its actual returned source and memo state.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- A finite first observation completes, fails, or reports its actual pending constructor. -/
inductive Terminal : Outcome width Symbol Guard A → Prop where
  | done (value : A) (state) : Terminal (.done value state)
  | failed (failure : Failure) (state) : Terminal (.failed failure state)
  | constructor (key : NodeKey) (code : Code Symbol Guard A) (state) : Terminal (.blocked (.constructor key) code state)

/-- An actual finite yielded prefix composes with a finite terminal continuation. -/
theorem terminal_after_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code next : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (trace : Steps emptyGuard conjoin fuel code state next after)
    (later : ∃ extra, Terminal (execute emptyGuard conjoin extra next after)) :
    ∃ total, Terminal (execute emptyGuard conjoin total code state) := by
  obtain ⟨extra, terminal⟩ := later
  refine ⟨fuel + extra, ?_⟩
  rw [execute_add, trace.execute, resume]
  exact terminal

/-- One actual yielded step composes with a finite terminal continuation. -/
theorem terminal_after_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code next : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (one : step emptyGuard conjoin code state = .yielded next after)
    (later : ∃ fuel, Terminal (execute emptyGuard conjoin fuel next after)) :
    ∃ fuel, Terminal (execute emptyGuard conjoin fuel code state) :=
  terminal_after_trace emptyGuard conjoin 1 code next state after (.cons _ _ _ _ _ _ 0 one (.refl _ _)) later

/-- An actual failed body retains its exact failure and complete native state through outer code. -/
theorem execute_bind_failed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (failure : Failure)
    (done : execute emptyGuard conjoin fuel code state = .failed failure after) :
    execute emptyGuard conjoin fuel (code.bind next) state = .failed failure after := by
  induction fuel generalizing code state with
  | zero => cases done
  | succ fuel ih =>
      cases one : step emptyGuard conjoin code state with
      | yielded rest current =>
          have tail : execute emptyGuard conjoin fuel rest current = .failed failure after := by
            simpa only [execute, one] using done
          simpa only [execute, step_bind, one, appendStep] using ih rest current tail
      | done value current | blocked reason rest current => simp only [execute, one] at done; cases done
      | failed actual current =>
          have same : Outcome.failed actual current = (Outcome.failed failure after : Outcome width Symbol Guard A) := by
            simpa only [execute, one] using done
          cases same
          simp only [execute, step_bind, one, appendStep]

/-- An actual pending constructor retains its exact remaining code and complete native state through outer code. -/
theorem execute_bind_constructor [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code remaining : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (key : NodeKey)
    (blocked : execute emptyGuard conjoin fuel code state = .blocked (.constructor key) remaining after) :
    execute emptyGuard conjoin fuel (code.bind next) state = .blocked (.constructor key) (remaining.bind next) after := by
  induction fuel generalizing code state with
  | zero => cases blocked
  | succ fuel ih =>
      cases one : step emptyGuard conjoin code state with
      | yielded rest current =>
          have tail : execute emptyGuard conjoin fuel rest current = .blocked (.constructor key) remaining after := by
            simpa only [execute, one] using blocked
          simpa only [execute, step_bind, one, appendStep] using ih rest current tail
      | done value current | failed failure current => simp only [execute, one] at blocked; cases blocked
      | blocked reason rest current =>
          have same : Outcome.blocked reason rest current = (Outcome.blocked (.constructor key) remaining after : Outcome width Symbol Guard A) := by
            simpa only [execute, one] using blocked
          cases same
          simp only [execute, step_bind, one, appendStep]

/-- A finite body observation composes with its actual returned continuation. -/
theorem terminal_bind [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (observed : ∃ fuel, Terminal (execute emptyGuard conjoin fuel code state))
    (continuation : ∀ fuel value after, execute emptyGuard conjoin fuel code state = .done value after →
      ∃ extra, Terminal (execute emptyGuard conjoin extra (next value) after)) :
    ∃ fuel, Terminal (execute emptyGuard conjoin fuel (code.bind next) state) := by
  obtain ⟨fuel, terminal⟩ := observed
  generalize done : execute emptyGuard conjoin fuel code state = actual at terminal
  cases terminal with
  | done value after =>
      obtain ⟨steps, _, trace⟩ := done_trace emptyGuard conjoin fuel code state after value done
      exact terminal_after_trace emptyGuard conjoin steps (code.bind next) (next value) state after
        (Steps.bind emptyGuard conjoin steps code (.pure value) state after trace next) (continuation fuel value after done)
  | failed failure after => exact ⟨fuel, by rw [execute_bind_failed emptyGuard conjoin fuel code next state after failure done]; exact .failed _ _⟩
  | constructor key remaining after =>
      exact ⟨fuel, by rw [execute_bind_constructor emptyGuard conjoin fuel code remaining next state after key done]; exact .constructor _ _ _⟩

end MicroCFTA.SourceRecursiveIntersectionNative
