import MicroCFTA.SourceDenotationEffects
import MicroCFTA.SourceSizedReference

/-!
# The denotation filter and first-occurrence term list

Runs stay in their enumerator order. Every residual list is checked before
term deduplication. The result therefore keeps the first accepted occurrence
of each term. A later duplicate can still stop evaluation with Unknown.
-/

namespace MicroCFTA.SourceDenotationRuns

open SourceDenotationEffects SourceSizedLiquidExecution

/-- Project accepted terms, then keep their first occurrences. -/
def finish [DecidableEq Value] (rows : List (Value × List Item)) : List Value :=
  SourceSizedReference.nub (rows.map Prod.fst)

/-- The constrained denotation branch consists of the residual filter followed by nubOrd. -/
inductive Run [DecidableEq Value] (evaluates : Item → Nat → SolverAdapter.Result → Prop)
    (rows : List (Value × List Item)) : Except (Halt Item) (List Value) → Nat → Prop where
  | done : SourceDenotationEffects.FilterRun evaluates rows result work →
      Run evaluates rows (result.map finish) (work + 1)

/-- Successful denotation has the exact original accepted-run order with first-occurrence deduplication. -/
theorem success_exact [DecidableEq Value] (evaluates : Item → Nat → SolverAdapter.Result → Prop)
    (holds : Item → Bool) (adequate : Adequate evaluates holds) (rows : List (Value × List Item))
    (output : List Value) (work : Nat) (run : Run evaluates rows (.ok output) work) :
    output = finish (rows.filter (fun row => row.2.all holds)) := by
  generalize resultEq : (Except.ok output : Except (Halt Item) (List Value)) = result at run
  cases run with
  | @done result work filtered =>
      cases result with
      | error bad => cases resultEq
      | ok kept =>
          have same := SourceDenotationEffects.filter_success evaluates holds adequate filtered kept rfl
          exact (Except.ok.inj resultEq).trans (congrArg finish same)

/-- The successful list contains a value exactly when one of its runs satisfies every residual. -/
theorem member_iff [DecidableEq Value] (evaluates : Item → Nat → SolverAdapter.Result → Prop)
    (holds : Item → Bool) (adequate : Adequate evaluates holds) (rows : List (Value × List Item))
    (output : List Value) (work : Nat) (run : Run evaluates rows (.ok output) work) (value : Value) :
    value ∈ output ↔ ∃ obligations, (value, obligations) ∈ rows ∧ ∀ item ∈ obligations, holds item = true := by
  rw [success_exact evaluates holds adequate rows output work run]
  simp only [finish, SourceSizedReference.mem_nub, List.mem_map, List.mem_filter, List.all_eq_true]
  constructor
  · rintro ⟨⟨found, obligations⟩, ⟨member, checked⟩, same⟩
    cases same
    exact ⟨obligations, member, checked⟩
  · rintro ⟨obligations, member, checked⟩
    exact ⟨(value, obligations), ⟨member, checked⟩, rfl⟩

/-- Every successful denotation result contains each term once. -/
theorem nodup [DecidableEq Value] (evaluates : Item → Nat → SolverAdapter.Result → Prop)
    (rows : List (Value × List Item)) (output : List Value) (work : Nat)
    (run : Run evaluates rows (.ok output) work) : output.Nodup := by
  generalize resultEq : (Except.ok output : Except (Halt Item) (List Value)) = result at run
  cases run with
  | @done result work filtered =>
      cases result with
      | error bad => cases resultEq
      | ok kept =>
          rw [Except.ok.inj resultEq]
          exact SourceSizedReference.nub_nodup _

/-- Finite enumerated rows and completed evaluator calls give a finite denotation outcome. -/
theorem finite [DecidableEq Value] (evaluates : Item → Nat → SolverAdapter.Result → Prop)
    (completed : ∀ item, ∃ work result, evaluates item work result) (rows : List (Value × List Item)) :
    ∃ result work, Run evaluates rows result work := by
  obtain ⟨result, work, filtered⟩ := SourceDenotationEffects.filter_finite evaluates completed rows
  exact ⟨result.map finish, work + 1, .done filtered⟩

/-- The exact first stop follows complete earlier runs and only Yes obligations in its own run. -/
theorem first_stop [DecidableEq Value] (evaluates : Item → Nat → SolverAdapter.Result → Prop)
    (rows : List (Value × List Item)) (bad : Halt Item) (work : Nat)
    (run : Run evaluates rows (.error bad) work) :
    ∃ earlier value obligations later kept priorWork,
      rows = earlier ++ (value, obligations) :: later ∧
      SourceDenotationEffects.FilterRun evaluates earlier (.ok kept) priorWork ∧
      ∃ before item after beforeWork stopWork,
        obligations = before ++ item :: after ∧ AllRun evaluates before (.ok true) beforeWork ∧
        Caused evaluates bad item stopWork := by
  generalize resultEq : (Except.error bad : Except (Halt Item) (List Value)) = result at run
  cases run with
  | @done result work filtered =>
      cases result with
      | ok kept => cases resultEq
      | error original =>
          cases Except.error.inj resultEq
          obtain ⟨earlier, row, later, kept, priorWork, checkWork, rowsEq, prior, failed⟩ :=
            SourceDenotationEffects.filter_first_stop evaluates filtered bad rfl
          exact ⟨earlier, row.1, row.2, later, kept, priorWork, rowsEq, prior,
            all_first_stop evaluates failed bad rfl⟩

end MicroCFTA.SourceDenotationRuns
