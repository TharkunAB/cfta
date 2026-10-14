import MicroCFTA.SourceRecursiveIntersectionNativeEffects

/-!
# Split actual completed native traces

A completed trace for appended code contains a finite completed inner body
and the remaining outer continuation. The split retains their exact shared
state and original total step count. No body result or memo provenance is
supplied as a premise.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- A zero-step trace retains its original control and every cache. -/
theorem steps_zero [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code next : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (trace : Steps emptyGuard conjoin 0 code state next after) : code = next ∧ state = after := by
  cases trace
  exact ⟨rfl, rfl⟩

/-- A positive trace exposes the exact original first step and remaining trace. -/
theorem steps_succ [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code next : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (trace : Steps emptyGuard conjoin (fuel + 1) code state next after) :
    ∃ (rest : Code Symbol Guard A) (current : SourceRecursiveIntersectionThunks.State width Symbol Guard),
      step emptyGuard conjoin code state = .yielded rest current ∧ Steps emptyGuard conjoin fuel rest current next after := by
  cases trace with
  | cons code state rest current next after fuel one tail => exact ⟨rest, current, one, tail⟩

/-- A pure value cannot make a yielded step, so its completed trace is empty. -/
theorem pure_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (first value : A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (trace : Steps emptyGuard conjoin fuel (.pure first) state (.pure value) after) : fuel = 0 ∧ first = value ∧ state = after := by
  cases trace with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | cons code state rest current final after fuel one tail => cases one

/-- Every completed appended trace derives its inner value, exact shared state, and finite continuation trace. -/
theorem steps_bind_inverse [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : B)
    (trace : Steps emptyGuard conjoin fuel (code.bind next) state (.pure value) after) :
    ∃ (inner outer : Nat) (result : A) (current : SourceRecursiveIntersectionThunks.State width Symbol Guard),
      inner + outer = fuel ∧ Steps emptyGuard conjoin inner code state (.pure result) current ∧
        Steps emptyGuard conjoin outer (next result) current (.pure value) after := by
  induction fuel generalizing code state with
  | zero =>
    have same := steps_zero emptyGuard conjoin _ _ _ _ trace
    cases code with
    | pure result => exact ⟨0, 0, result, state, rfl, .refl _ _, trace⟩
    | fail | work | enter | read | optionalBinder | node | edge | finishNode | finishEdge => cases same.1
  | succ fuel ih =>
    obtain ⟨rest, current, oneBound, tail⟩ := steps_succ emptyGuard conjoin fuel _ _ _ _ trace
    have boundStep := step_bind emptyGuard conjoin code next state
    cases one : step emptyGuard conjoin code state with
    | done result initial =>
      obtain ⟨pure, retained⟩ := (step_done_iff emptyGuard conjoin code state initial result).mp one
      subst code
      subst initial
      exact ⟨0, fuel + 1, result, state, by omega, .refl _ _, trace⟩
    | yielded body middle =>
      rw [one, appendStep] at boundStep
      have same := Outcome.yielded.inj (boundStep.symm.trans oneBound)
      rcases same.1 with rfl
      rcases same.2 with rfl
      obtain ⟨inner, outer, result, final, count, bodyTrace, outerTrace⟩ := ih body middle tail
      exact ⟨inner + 1, outer, result, final, by omega, .cons _ _ _ _ _ _ _ one bodyTrace, outerTrace⟩
    | failed failure middle | blocked reason body middle =>
      rw [one, appendStep] at boundStep
      have impossible := boundStep.symm.trans oneBound
      cases impossible

/-- A node completion frame consumes one step at its exact updated memo state. -/
theorem finishNode_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (handle : Nat) (result : Value Symbol Guard) (next : Code Symbol Guard A)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : A)
    (trace : Steps emptyGuard conjoin fuel (.finishNode handle result next) state (.pure value) after) :
    ∃ rest, fuel = rest + 1 ∧ Steps emptyGuard conjoin rest next (SourceRecursiveIntersectionThunks.finishNode handle result state) (.pure value) after := by
  cases fuel with
  | zero => cases (steps_zero emptyGuard conjoin _ _ _ _ trace).1
  | succ fuel =>
    obtain ⟨code, current, one, tail⟩ := steps_succ emptyGuard conjoin fuel _ _ _ _ trace
    have same := Outcome.yielded.inj one
    rcases same.1 with rfl
    rcases same.2 with rfl
    exact ⟨fuel, rfl, tail⟩

/-- An edge completion frame consumes one step at its exact updated memo state. -/
theorem finishEdge_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (handle : Nat) (result : EdgeValue Symbol Guard) (next : Code Symbol Guard A)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : A)
    (trace : Steps emptyGuard conjoin fuel (.finishEdge handle result next) state (.pure value) after) :
    ∃ rest, fuel = rest + 1 ∧ Steps emptyGuard conjoin rest next (SourceRecursiveIntersectionThunks.finishEdge handle result state) (.pure value) after := by
  cases fuel with
  | zero => cases (steps_zero emptyGuard conjoin _ _ _ _ trace).1
  | succ fuel =>
    obtain ⟨code, current, one, tail⟩ := steps_succ emptyGuard conjoin fuel _ _ _ _ trace
    have same := Outcome.yielded.inj one
    rcases same.1 with rfl
    rcases same.2 with rfl
    exact ⟨fuel, rfl, tail⟩

end MicroCFTA.SourceRecursiveIntersectionNative
