import MicroCFTA.SourceEqualityConstraintConstructors

/-!
# Independent PCS meaning for complete source constraints

Raw PCS classes equate distinct paths. Singleton classes impose no condition.
The current public existence-sensitive indicator agrees on active source
payloads. Actual source normalization preserves the independent PCS meaning
without a representation premise on arbitrary raw classes.
-/
namespace MicroCFTA.SourceEqualityPCSGuard
open Language EqualityNormalize SourceObservations SourceGuards SourceSymbolicIndex
open SourceCompactGuards SourceEqualityGuardReadback

/-- Completed source equality payload readback has its independent PCS meaning. -/
theorem result_sat (term : Term Symbol) (result : RunResult) :
    Sat term (SymbolicEqualityBridge.resultClasses result) ↔ RunSat term result := by cases result <;> rfl

/-- The actual finite source array normalizer preserves raw PCS meaning, including trivial classes. -/
theorem normalize_sat (classes : Constraints) (term : Term Symbol) : Sat term (normalize classes) ↔ Satisfies term classes := by
  unfold normalize
  rw [arrayNormalize_eq, result_sat]
  exact EqualityTermination.mkEqConstraints_total_correct term classes

/-- Source equality combination denotes PCS conjunction for every raw payload. -/
theorem combine_sat (first second : Option Constraints) (term : Term Symbol) :
    Sat term (combineEqualities first second) ↔ Sat term first ∧ Sat term second := by
  cases first with
  | none => simp [combineEqualities, Sat]
  | some first => cases second with
    | none => simp [combineEqualities, Sat]
    | some second =>
        have exact := normalize_sat (first ++ second) term
        cases first <;> cases second
        · simp [combineEqualities, Sat, Satisfies]
        all_goals simpa only [combineEqualities, Sat, Satisfies, List.mem_append, or_imp, forall_and] using exact

/-- Complete independent constraints retain raw PCS equalities and the actual public guard decision. -/
noncomputable def holds [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (term : Term (Label Formula)) : Bool := by
  classical
  exact decide (Sat term constraint.equalities) && decide (SourceBooleanEntry.evaluateGuard formulas solver constraint.guard term = .yes)

/-- The complete independent constraint test has exactly its two intended conjuncts. -/
theorem holds_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (term : Term (Label Formula)) :
    holds formulas solver constraint term = true ↔ Sat term constraint.equalities ∧ SourceBooleanEntry.evaluateGuard formulas solver constraint.guard term = .yes := by
  simp only [holds, Bool.and_eq_true_iff, decide_eq_true_eq]

/-- Independent PCS constraints and current public indicators agree on every active source payload. -/
theorem public_eq [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (stored : ActiveOption constraint.equalities) (term : Term (Label Formula)) :
    holds formulas solver constraint term = acceptsConstraint formulas solver constraint term := by
  apply Bool.eq_iff_iff.mpr
  rw [holds_exact]
  simp only [acceptsConstraint, Bool.and_eq_true_iff, decide_eq_true_eq]
  exact and_congr (value_exact term constraint.equalities stored).symm Iff.rfl

/-- Positive guard normalization supplies exactly its independent completed class meaning. -/
theorem positive_sat [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (guard : Guard Formula) (raw : Constraints) (extracted : positive guard = some raw) :
    ∃ added, positiveNormalized guard = some added ∧
      ∀ term : Term (Label Formula), Sat term added ↔ SourceBooleanEntry.evaluateGuard formulas solver guard term = .yes := by
  obtain ⟨added, found, active, exact⟩ := positiveNormalized_exact (Symbol := Label Formula) guard raw extracted
  refine ⟨added, found, ?_⟩
  intro term
  exact ((value_exact term added active).symm.trans (by rw [exact term])).trans (positive_exact formulas solver guard raw extracted term).symm

/-- At positive source guards, the actual accessor has complete independent PCS constraint meaning. -/
theorem positive_source [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (positiveGuard : (positive constraint.guard).isSome = true) (term : Term (Label Formula)) :
    holds formulas solver constraint term = true ↔ Sat term (sourceEqualities constraint) := by
  obtain ⟨raw, extracted⟩ := Option.isSome_iff_exists.mp positiveGuard
  obtain ⟨added, found, exact⟩ := positive_sat formulas solver constraint.guard raw extracted
  rw [holds_exact, ← exact term]
  unfold sourceEqualities
  rw [found]
  cases added with
  | none => simpa only [combine_sat, Sat, and_false] using (combine_sat constraint.equalities none term).symm
  | some classes => cases classes with
    | nil => simp [Sat, Satisfies]
    | cons first rest => exact (combine_sat constraint.equalities (some (first :: rest)) term).symm

/-- Complete independent guard acceptance implies the actual own payload for positive and residual guards. -/
theorem own_sat [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (term : Term (Label Formula)) (accepted : holds formulas solver constraint term = true) :
    Sat term (sourceEqualities constraint) := by
  by_cases positiveGuard : (positive constraint.guard).isSome = true
  · exact (positive_source formulas solver constraint positiveGuard term).mp accepted
  · have missing : positiveNormalized constraint.guard = none := by
      cases found : positiveNormalized constraint.guard with
      | none => rfl
      | some result =>
          have support := positiveNormalized_support constraint.guard
          rw [found] at support
          exact False.elim (positiveGuard support.symm)
    simpa only [sourceEqualities, missing] using ((holds_exact formulas solver constraint term).mp accepted).1

end MicroCFTA.SourceEqualityPCSGuard
