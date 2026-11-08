import MicroCFTA.SourceCurrentConjunctionTuplePullCompletion
import MicroCFTA.SourceCurrentConjunctionTuplePullTotalEffects

/-!
# Successful total sampling from initial closed operands

Cursor induction derives a finite successful read allowance from current
physical invariants. Each continuation uses its actual returned heap. A
maximum retains the same successful prefix and continuation. This result
is existential. It does not supply a numeric native runtime bound.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullTotalCompletion
open InternedConstructorTemplates
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionTuplePull (Cursor Event start step)
open SourceCurrentConjunctionTuplePullEffects (Inputs EventInputs)
open SourceCurrentConjunctionTuplePullClosed (ClosedOperands start_closed next_closed)
open SourceCurrentConjunctionTuplePullProgress (wellFounded step_next)
open SourceCurrentConjunctionTuplePullTotal (Result run sample)
open SourceCurrentConjunctionTuplePullDriveEffects (StatusInputs)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem run_done (budget : Nat) (cursor : Cursor Symbol Formula) :
    ∀ (collected : List (List Edge)) (before : Physical Symbol Formula),
      Ready before → Inputs before.heap cursor → ClosedOperands cursor →
      ∃ h result after, run h budget cursor collected before = .done result after ∧ Effects before after := by
  apply wellFounded.induction cursor
  intro cursor ih collected before ready inputs closed
  obtain ⟨headH, event, middle, stable, effects, supported⟩ :=
    SourceCurrentConjunctionTuplePullCompletion.step_complete cursor before ready inputs closed
  have actual := stable headH (Nat.le_refl _)
  cases event with
  | ended =>
      exact ⟨headH, .fit collected, middle,
        by rw [SourceCurrentConjunctionTuplePullTotal.run_eq, actual], effects⟩
  | more next =>
      have smaller := step_next headH cursor before middle (.more next) actual
      obtain ⟨tailH, result, after, completed, tailEffects⟩ :=
        ih next smaller collected middle effects.ready supported (next_closed smaller closed)
      refine ⟨max headH tailH, result, after, ?_, effects.trans tailEffects⟩
      rw [SourceCurrentConjunctionTuplePullTotal.run_eq, stable _ (Nat.le_max_left _ _)]
      exact SourceCurrentConjunctionTuplePullStability.run_done_stable completed (Nat.le_max_right _ _)
  | yield tuple next =>
      by_cases full : budget < (collected ++ [tuple]).length
      · refine ⟨headH, .overflow (collected ++ [tuple]) next, middle, ?_, effects⟩
        rw [SourceCurrentConjunctionTuplePullTotal.run_eq, actual]
        simp only [full, ite_true]
      · have smaller := step_next headH cursor before middle (.yield tuple next) actual
        obtain ⟨tailH, result, after, completed, tailEffects⟩ :=
          ih next smaller (collected ++ [tuple]) middle effects.ready supported.2 (next_closed smaller closed)
        refine ⟨max headH tailH, result, after, ?_, effects.trans tailEffects⟩
        rw [SourceCurrentConjunctionTuplePullTotal.run_eq, stable _ (Nat.le_max_left _ _)]
        simp only [full, ite_false]
        exact SourceCurrentConjunctionTuplePullStability.run_done_stable completed (Nat.le_max_right _ _)

/-- Initial cursor invariants derive successful total execution at one stable read allowance. -/
theorem run_complete (budget : Nat) (cursor : Cursor Symbol Formula) (collected : List (List Edge))
    (before : Physical Symbol Formula) (ready : Ready before) (inputs : Inputs before.heap cursor)
    (closed : ClosedOperands cursor) :
    ∃ h result after,
      (∀ H, h ≤ H → run H budget cursor collected before = .done result after) ∧ Effects before after := by
  obtain ⟨h, result, after, actual, effects⟩ := run_done budget cursor collected before ready inputs closed
  exact ⟨h, result, after,
    fun _ enough => SourceCurrentConjunctionTuplePullStability.run_done_stable actual enough, effects⟩

/-- Initial closed operands derive a stable full sample, its effects, residents, and exact cap. -/
theorem sample_complete (budget : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes) :
    ∃ h result after,
      (∀ H, h ≤ H → sample H budget nodes before = .done result after) ∧
      Effects before after ∧ StatusInputs after.heap result.toStatus ∧
      SourceCurrentConjunctionTuplePullAdmission.Bounded budget result.toStatus := by
  obtain ⟨h, result, after, stable, effects⟩ := run_complete budget (start nodes) [] before ready
    (SourceCurrentConjunctionTuplePullEffects.start_inputs before.heap nodes available) (start_closed nodes closed)
  have actual : sample h budget nodes before = .done result after := stable h (Nat.le_refl _)
  have retained := SourceCurrentConjunctionTuplePullTotalEffects.sample_effects h budget nodes before ready available
  exact ⟨h, result, after, stable, effects, retained.2 result after actual,
    SourceCurrentConjunctionTuplePullTotal.sample_bounded h budget nodes before after result actual⟩

end MicroCFTA.SourceCurrentConjunctionTuplePullTotalCompletion
