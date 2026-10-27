import MicroCFTA.SourceEqualityNativeDemandTrace

/-!
# Split completed checked native demand

A completed appended trace contains an actual inner trace and an actual
continuation trace. Their common state retains both native memo families
and all constraint-operation caches. The split derives the inner result
from execution. It does not assume a future child answer.
-/
namespace MicroCFTA.SourceEqualityNativeDemand
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- A zero-step trace retains its original control and complete state. -/
theorem steps_zero [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control next : Control Output) (state after : State width) (trace : Steps 0 control state next after) :
    control = next ∧ state = after := by
  cases trace
  exact ⟨rfl, rfl⟩

/-- A positive trace exposes its actual first yielded step and remaining trace. -/
theorem steps_succ [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control next : Control Output) (state after : State width)
    (trace : Steps (fuel + 1) control state next after) :
    ∃ rest current, step control state = .yielded rest current ∧ Steps fuel rest current next after := by
  cases trace with
  | cons control state rest current next after fuel one tail => exact ⟨rest, current, one, tail⟩

/-- A pure value cannot yield, so its trace to a pure result is empty. -/
theorem pure_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (first value : Output) (state after : State width)
    (trace : Steps fuel (.code (.pure first)) state (.code (.pure value)) after) :
    fuel = 0 ∧ first = value ∧ state = after := by
  cases trace with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | cons control state rest current final after fuel one tail => cases one

/-- An appended completed trace derives both actual traces and preserves their total step count. -/
theorem steps_bind_inverse [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control A) (next : A → Code Symbol Guard B)
    (state after : State width) (value : B)
    (trace : Steps fuel (control.bind next) state (.code (.pure value)) after) :
    ∃ (inner outer : Nat) (result : A) (current : State width),
      inner + outer = fuel ∧ Steps inner control state (.code (.pure result)) current ∧
        Steps outer (.code (next result)) current (.code (.pure value)) after := by
  induction fuel generalizing control state with
  | zero =>
      have same := steps_zero _ _ _ _ trace
      cases control with
      | edgeBody => cases same.1
      | code code =>
          cases code with
          | pure result => exact ⟨0, 0, result, state, rfl, .refl _ _, trace⟩
          | fail | work | enter | read | optionalBinder | node | edge | finishNode | finishEdge => cases same.1
  | succ fuel ih =>
      obtain ⟨rest, current, oneBound, tail⟩ := steps_succ fuel _ _ _ _ trace
      have boundStep := step_bind control next state
      cases one : step control state with
      | done result initial =>
          obtain ⟨pure, retained⟩ := (step_done_iff control state initial result).mp one
          subst control
          subst initial
          exact ⟨0, fuel + 1, result, state, by omega, .refl _ _, trace⟩
      | yielded body middle =>
          rw [one, appendStep] at boundStep
          have same := Outcome.yielded.inj (boundStep.symm.trans oneBound)
          rcases same.1 with rfl
          rcases same.2 with rfl
          obtain ⟨inner, outer, result, final, count, bodyTrace, outerTrace⟩ := ih body middle tail
          exact ⟨inner + 1, outer, result, final, by omega, .cons _ _ _ _ _ _ _ one bodyTrace, outerTrace⟩
      | failed failure middle | constraintError message middle | blocked reason body middle =>
          rw [one, appendStep] at boundStep
          have impossible := boundStep.symm.trans oneBound
          cases impossible

/-- A completed appended run derives the actual inner result and its remaining completed continuation. -/
theorem done_bind_cases [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control A) (next : A → Code Symbol Guard B)
    (state after : State width) (value : B)
    (done : execute fuel (control.bind next) state = .done value after) :
    ∃ (steps : Nat) (result : A) (current : State width),
      Steps steps control state (.code (.pure result)) current ∧
        ∃ tailfuel, execute tailfuel (.code (next result)) current = .done value after := by
  obtain ⟨total, _, trace⟩ := done_trace fuel (control.bind next) state after value done
  obtain ⟨inner, outer, result, current, _, innerTrace, outerTrace⟩ :=
    steps_bind_inverse total control next state after value trace
  exact ⟨inner, result, current, innerTrace, outer + 1,
    trace_done outer (.code (next result)) current after value outerTrace⟩

end MicroCFTA.SourceEqualityNativeDemand
