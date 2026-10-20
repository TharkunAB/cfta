import MicroCFTA.SourceEqualityNativeDemandContinuation

/-!
# Finite traces for actual checked native demand

Each trace records actual yielded controls and their complete states.
Traces compose and retain appended source continuations. Completion gives
a finite trace to the returned pure value. This does not assert that every
source request completes.
-/
namespace MicroCFTA.SourceEqualityNativeDemand
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- A finite trace retains every actual yielded control and its complete state. -/
inductive Steps [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → Control Output → State width → Control Output → State width → Prop where
  | refl (control state) : Steps 0 control state control state
  | cons (control state next after final result fuel)
      (step : SourceEqualityNativeDemand.step control state = .yielded next after)
      (rest : Steps fuel next after final result) : Steps (fuel + 1) control state final result

/-- Every yielded trace gives the exact original bounded execution. -/
theorem Steps.execute [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control next : Control Output) (state after : State width)
    (trace : Steps fuel control state next after) : execute fuel control state = .yielded next after := by
  induction trace with
  | refl => rfl
  | cons control state next after final result fuel one rest ih =>
      simp only [SourceEqualityNativeDemand.execute, one]
      exact ih

/-- A yielded run derives the exact intermediate trace without an assumed execution plan. -/
theorem execute_steps [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control next : Control Output) (state after : State width)
    (yielded : execute fuel control state = .yielded next after) : Steps fuel control state next after := by
  induction fuel generalizing control state with
  | zero =>
      have same := Outcome.yielded.inj yielded
      rcases same.1 with rfl
      rcases same.2 with rfl
      exact .refl _ _
  | succ fuel ih =>
      cases one : step control state with
      | yielded rest current =>
          have remaining : execute fuel rest current = .yielded next after := by
            simpa only [execute, one] using yielded
          exact .cons _ _ _ _ _ _ _ one (ih rest current remaining)
      | done | failed | constraintError | blocked => simp only [execute, one] at yielded; cases yielded

/-- Yielded traces compose at their exact common control and state. -/
theorem Steps.trans [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (first second : Nat) (control middle next : Control Output) (state current after : State width)
    (earlier : Steps first control state middle current) (later : Steps second middle current next after) :
    Steps (first + second) control state next after := by
  apply execute_steps
  rw [execute_add, earlier.execute, resume]
  exact later.execute

/-- An appended continuation retains every original yielded control and complete state. -/
theorem Steps.bind [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control rest : Control A) (state after : State width)
    (trace : Steps fuel control state rest after) (next : A → Code Symbol Guard B) :
    Steps fuel (control.bind next) state (rest.bind next) after := by
  induction trace with
  | refl => exact .refl _ _
  | cons control state middle current final result fuel one tail ih =>
      apply Steps.cons _ _ _ _ _ _ _
      · rw [step_bind, one]
        rfl
      · exact ih

private theorem body_ne_done (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard Output) (state after : State width) (value : Output) :
    body request next state ≠ .done value after := by
  unfold body
  split
  · intro impossible; cases impossible
  · split
    · intro impossible; cases impossible
    · intro impossible; cases impossible
    · split
      · intro impossible; cases impossible
      · intro impossible; cases impossible
      · dsimp only
        split <;> intro impossible <;> cases impossible

/-- Only a pure code control can complete one checked native step. -/
theorem step_done_iff [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control Output) (state after : State width) (value : Output) :
    step control state = .done value after ↔ control = .code (.pure value) ∧ state = after := by
  cases control with
  | edgeBody request next => simp only [step, body_ne_done, reduceCtorEq, false_and]
  | code code =>
      cases code with
      | pure result =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift, Outcome.done.injEq,
            Control.code.injEq, Code.pure.injEq]
      | fail | work | enter | read | finishNode | finishEdge =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift, Control.code.injEq, reduceCtorEq, false_and]
      | optionalBinder key body next =>
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.native.machine.heap <;>
            simp only [step, SourceRecursiveIntersectionNative.step, actual, lift, Control.code.injEq,
              reduceCtorEq, false_and]
      | node request next =>
          cases selected : lookupNode width request state.native with
          | mk selection current =>
              cases selection with
              | direct actual =>
                  simp only [step, SourceRecursiveIntersectionNative.step, selected, lift,
                    Control.code.injEq, reduceCtorEq, false_and]
              | memoized handle =>
                  cases demanded : demandNode handle current with
                  | mk observation final =>
                      cases observation <;> simp only [step, SourceRecursiveIntersectionNative.step,
                        selected, demanded, lift, Control.code.injEq, reduceCtorEq, false_and]
      | edge request next =>
          cases selected : lookupEdge width request state.native with
          | mk handle current =>
              cases demanded : demandEdge handle current with
              | mk observation final =>
                  cases observation <;> simp only [step, selected, demanded, Control.code.injEq, reduceCtorEq, false_and]

/-- An actual completed run derives a bounded exact trace to its returned pure value. -/
theorem done_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (state after : State width) (value : Output)
    (done : execute fuel control state = .done value after) :
    ∃ steps, steps < fuel ∧ Steps steps control state (.code (.pure value)) after := by
  induction fuel generalizing control state with
  | zero => cases done
  | succ fuel ih =>
      cases one : step control state with
      | done result current =>
          have same := Outcome.done.inj (by simpa only [execute, one] using done)
          rcases same.1 with rfl
          rcases same.2 with rfl
          have pure := (step_done_iff control state current result).mp one
          rcases pure.1 with rfl
          rcases pure.2 with rfl
          exact ⟨0, by omega, .refl _ _⟩
      | yielded next current =>
          obtain ⟨steps, bounded, trace⟩ := ih next current (by simpa only [execute, one] using done)
          exact ⟨steps + 1, by omega, .cons _ _ _ _ _ _ _ one trace⟩
      | failed | constraintError | blocked => simp only [execute, one] at done; cases done

/-- A trace to a pure value completes with that exact result after one further step. -/
theorem trace_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (state after : State width) (value : Output)
    (trace : Steps fuel control state (.code (.pure value)) after) :
    execute (fuel + 1) control state = .done value after := by
  rw [execute_add, trace.execute]
  rfl

end MicroCFTA.SourceEqualityNativeDemand
