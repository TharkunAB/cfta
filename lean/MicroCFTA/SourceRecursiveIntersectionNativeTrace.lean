import MicroCFTA.SourceRecursiveIntersectionNativeContinuation

/-!
# Finite native execution traces

Traces contain actual yielded steps and their exact intermediate source and
memo caches. They characterize bounded execution and compose with retained
continuations. A completed run reaches its returned pure value after a finite
trace. This does not prove that every request completes.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- A finite trace retains every actual yielded native step and intermediate cache. -/
inductive Steps [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
    Nat → Code Symbol Guard A → SourceRecursiveIntersectionThunks.State width Symbol Guard →
      Code Symbol Guard A → SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop where
  | refl (code state) : Steps emptyGuard conjoin 0 code state code state
  | cons (code state next after final result fuel)
      (step : SourceRecursiveIntersectionNative.step emptyGuard conjoin code state = .yielded next after)
      (rest : Steps emptyGuard conjoin fuel next after final result) :
      Steps emptyGuard conjoin (fuel + 1) code state final result

/-- Every finite yielded trace is the exact original bounded native execution. -/
theorem Steps.execute [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code next : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (trace : Steps emptyGuard conjoin fuel code state next after) :
    execute emptyGuard conjoin fuel code state = .yielded next after := by
  induction trace with
  | refl => rfl
  | cons code state next after final result fuel one rest ih =>
    simp only [SourceRecursiveIntersectionNative.execute, one]
    exact ih

/-- A yielded bounded run derives all actual intermediate steps without an assumed trace. -/
theorem execute_steps [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code next : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (yielded : execute emptyGuard conjoin fuel code state = .yielded next after) :
    Steps emptyGuard conjoin fuel code state next after := by
  induction fuel generalizing code state with
  | zero =>
    have same := Outcome.yielded.inj yielded
    rcases same.1 with rfl
    rcases same.2 with rfl
    exact .refl _ _
  | succ fuel ih =>
    cases one : step emptyGuard conjoin code state with
    | yielded rest current =>
      have remaining : execute emptyGuard conjoin fuel rest current = .yielded next after := by
        simpa only [execute, one] using yielded
      exact .cons _ _ _ _ _ _ _ one (ih rest current remaining)
    | done | failed | blocked => simp only [execute, one] at yielded; cases yielded

/-- Native yielded traces compose at the exact preceding returned state. -/
theorem Steps.trans [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (first second : Nat) (code middle next : Code Symbol Guard A)
    (state current after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (earlier : Steps emptyGuard conjoin first code state middle current) (later : Steps emptyGuard conjoin second middle current next after) :
    Steps emptyGuard conjoin (first + second) code state next after := by
  apply execute_steps
  rw [execute_add, earlier.execute, resume]
  exact later.execute

/-- Appending an outer continuation preserves every original yielded step and exact cache. -/
theorem Steps.bind [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code rest : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (trace : Steps emptyGuard conjoin fuel code state rest after) (next : A → Code Symbol Guard B) :
    Steps emptyGuard conjoin fuel (code.bind next) state (rest.bind next) after := by
  induction trace with
  | refl => exact .refl _ _
  | cons code state middle current final result fuel one tail ih =>
    apply Steps.cons _ _ _ _ _ _ _
    · rw [step_bind, one]
      rfl
    · exact ih

/-- Only a pure value can complete one native step. -/
theorem step_done_iff [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : A) :
    step emptyGuard conjoin code state = .done value after ↔ code = .pure value ∧ state = after := by
  cases code with
  | pure result => simp only [step, Outcome.done.injEq, Code.pure.injEq]
  | fail failure | work job next | enter domain left right first second next | read name next | finishNode handle result next | finishEdge handle result next =>
    simp only [step, reduceCtorEq, false_and]
  | optionalBinder key body next =>
    cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap <;> simp only [step, actual, reduceCtorEq, false_and]
  | node request next =>
    cases selected : lookupNode width request state with
    | mk selection current =>
      cases selection with
      | direct actual => simp only [step, selected, reduceCtorEq, false_and]
      | memoized handle =>
        cases demanded : demandNode handle current with
        | mk observation final =>
          cases observation <;> simp only [step, selected, demanded, reduceCtorEq, false_and]
  | edge request next =>
    cases selected : lookupEdge width request state with
    | mk handle current =>
      cases demanded : demandEdge handle current with
      | mk observation final =>
        cases observation <;> simp only [step, selected, demanded, reduceCtorEq, false_and]

/-- A completed native run derives a finite exact trace to its returned pure value. -/
theorem done_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (value : A) (done : execute emptyGuard conjoin fuel code state = .done value after) :
    ∃ steps, steps < fuel ∧ Steps emptyGuard conjoin steps code state (.pure value) after := by
  induction fuel generalizing code state with
  | zero => cases done
  | succ fuel ih =>
    cases one : step emptyGuard conjoin code state with
    | done result current =>
      have same := Outcome.done.inj (by simpa only [execute, one] using done)
      rcases same.1 with rfl
      rcases same.2 with rfl
      have pure := (step_done_iff emptyGuard conjoin code state current result).mp one
      rcases pure.1 with rfl
      rcases pure.2 with rfl
      exact ⟨0, by omega, .refl _ _⟩
    | yielded next current =>
      obtain ⟨steps, bounded, trace⟩ := ih next current (by simpa only [execute, one] using done)
      exact ⟨steps + 1, by omega, .cons _ _ _ _ _ _ _ one trace⟩
    | failed | blocked => simp only [execute, one] at done; cases done

/-- A finite trace to a pure value produces that exact native result with one further step. -/
theorem trace_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (value : A) (trace : Steps emptyGuard conjoin fuel code state (.pure value) after) :
    execute emptyGuard conjoin (fuel + 1) code state = .done value after := by
  rw [execute_add, trace.execute]
  rfl

end MicroCFTA.SourceRecursiveIntersectionNative
