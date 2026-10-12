import MicroCFTA.ActualQuotient

/-!
# Sparse guard decisions refine complete guard decisions

The proof covers every source guard constructor and nested substitution.
The source table equality theorem discharges allocation when the sparse
ambiguity set is empty. Unknown remains a permitted loss of information.
-/
namespace MicroCFTA.SourceGuardRefinement
open SourceGuards SourceObservations Guards

/-- A sparse decision may lose information but cannot change a decided verdict. -/
def Refines (sparse complete : Verdict) : Prop := sparse = .unknown ∨ sparse = complete

theorem refines_refl (verdict : Verdict) : Refines verdict verdict := Or.inr rfl

theorem polarize_refines (positive : Bool) (sparse complete : Verdict)
    (refined : Refines sparse complete) : Refines (polarize positive sparse) (polarize positive complete) := by
  cases positive <;> cases sparse <;> cases complete <;> simp_all [Refines, polarize, Guards.negate]

theorem conjunction_refines (a b c d : Verdict) (first : Refines a c) (second : Refines b d) :
    Refines (Guards.conjunction a b) (Guards.conjunction c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [Refines, Guards.conjunction]

theorem disjunction_refines (a b c d : Verdict) (first : Refines a c) (second : Refines b d) :
    Refines (Guards.disjunction a b) (Guards.disjunction c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [Refines, Guards.disjunction]

theorem combine_cons (conjunctive : Bool) (head : Verdict) (rest : List Verdict) :
    combine conjunctive (head :: rest) = if conjunctive then
      Guards.conjunction head (combine conjunctive rest) else Guards.disjunction head (combine conjunctive rest) := by
  cases conjunctive <;> cases head <;> rfl

/-- The source's short-circuit Boolean fold preserves the verdict information order. -/
theorem combine_map_refines (conjunctive : Bool) (items : List α) (sparse complete : α → Verdict)
    (refined : ∀ item ∈ items, Refines (sparse item) (complete item)) :
    Refines (combine conjunctive (items.map sparse)) (combine conjunctive (items.map complete)) := by
  induction items with
  | nil => exact refines_refl _
  | cons item rest ih =>
      simp only [List.map_cons, combine_cons]
      have first := refined item (by simp)
      have tail := ih (fun value member => refined value (by simp [member]))
      cases conjunctive
      · exact disjunction_refines _ _ _ _ first tail
      · exact conjunction_refines _ _ _ _ first tail

/-- Complete source control is monotone in its structural equality callback, for fixed actual tables. -/
theorem evaluate_refines (formulas : Formulas Formula) (solver : SourceGuards.Entailment Formula)
    (observed : Observations Formula)
    (sparse complete : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (oracle : ∀ scopes left right answer, sparse scopes left right = some answer →
      complete scopes left right = some answer)
    (fresh : List (Path × (Name × Name))) (unknown : List Path)
    (scopes : List (List (Resolved Formula))) (positive : Bool) (guard : SourceGuards.Guard Formula) :
    Refines (evaluateWith formulas solver observed sparse fresh unknown scopes positive guard)
      (evaluateWith formulas solver observed complete fresh unknown scopes positive guard) := by
  cases guard with
  | top | bottom | entails _ _ | satisfies _ _ | holds _ _ =>
      simp only [evaluateWith]
      exact refines_refl _
  | same left right =>
      cases first : observed left <;> cases second : observed right <;>
        simp only [evaluateWith, first, second]
      all_goals try exact refines_refl _
      by_cases equal : left = right
      · simp only [equal, ↓reduceIte]
        exact refines_refl _
      · simp only [equal, ↓reduceIte]
        apply polarize_refines
        cases found : sparse scopes left right with
        | none => exact Or.inl rfl
        | some answer =>
            rw [oracle scopes left right answer found]
            exact refines_refl _
  | substitute additions inner =>
      simp only [evaluateWith]
      cases resolved : resolveMany formulas observed fresh unknown additions with
      | none => exact refines_refl _
      | some added => exact evaluate_refines formulas solver observed sparse complete oracle fresh unknown (added :: scopes) positive inner
  | not inner =>
      simp only [evaluateWith]
      exact evaluate_refines formulas solver observed sparse complete oracle fresh unknown scopes (!positive) inner
  | and parts =>
      simp only [evaluateWith]
      apply combine_map_refines positive parts
      intro part member
      exact evaluate_refines formulas solver observed sparse complete oracle fresh unknown scopes positive part
  | or parts =>
      simp only [evaluateWith]
      apply combine_map_refines (!positive) parts
      intro part member
      exact evaluate_refines formulas solver observed sparse complete oracle fresh unknown scopes positive part
termination_by sizeOf guard

/-- Every unambiguous sparse guard decision agrees with complete evaluation whenever it is decided. -/
theorem unambiguous_evaluator_refines [DecidableEq Formula] (formulas : Formulas Formula)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula))
    (guard : SourceGuards.Guard Formula)
    (unambiguous : ambiguous (observe term) (sameShape formulas (observe term) []) guard = []) :
    Refines (evaluateGuardWithShape formulas solver (observe term) guard)
      (evaluateGuard formulas solver guard term) := by
  unfold evaluateGuardWithShape evaluateGuard evaluateGuardWithSame
  rw [ActualQuotient.unambiguous_tables_equal formulas term guard unambiguous]
  exact evaluate_refines formulas solver (observe term) _ _
    (fun scopes left right answer => sameShape_sound formulas term scopes left right answer) _ _ [] true guard

/-- A decided unambiguous sparse result is exactly the complete-term evaluator result. -/
theorem unambiguous_decided_exact [DecidableEq Formula] (formulas : Formulas Formula)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula))
    (guard : SourceGuards.Guard Formula)
    (unambiguous : ambiguous (observe term) (sameShape formulas (observe term) []) guard = [])
    (decided : evaluateGuardWithShape formulas solver (observe term) guard ≠ .unknown) :
    evaluateGuardWithShape formulas solver (observe term) guard = evaluateGuard formulas solver guard term := by
  rcases unambiguous_evaluator_refines formulas solver term guard unambiguous with unknown | equal
  · exact False.elim (decided unknown)
  · exact equal

end MicroCFTA.SourceGuardRefinement
