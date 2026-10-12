import MicroCFTA.GuardConjunction

/-!
# Current public guard entry

Outer Boolean operands allocate independent actual-value tables. Nonempty
substitutions keep the scoped evaluator and its complete nested table.
`SourceGuards.evaluateGuardWithSame` is the historical whole-guard entry. It
also describes the current private `evaluateScopedGuard` helper exactly.
-/
namespace MicroCFTA.SourceBooleanEntry
open SourceGuards SourceObservations
open Guards (Verdict negate)

/-- Apply source polarity before entering one allocation scope. -/
def signed (positive : Bool) (guard : Guard Formula) : Guard Formula :=
  if positive then guard else .not guard

/-- The current private helper retains the original scoped evaluator. -/
def evaluateScoped [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) (guard : Guard Formula) : Verdict :=
  SourceGuards.evaluateGuardWithSame formulas solver observed sameAt (signed positive guard)

/-- The source public dispatcher stops only at nonempty scopes and atoms. -/
def evaluate [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) : Guard Formula → Verdict
  | .and parts => combine positive (parts.map (evaluate formulas solver observed sameAt positive))
  | .or parts => combine (!positive) (parts.map (evaluate formulas solver observed sameAt positive))
  | .not inner => evaluate formulas solver observed sameAt (!positive) inner
  | .substitute [] inner => evaluate formulas solver observed sameAt positive inner
  | guard => evaluateScoped formulas solver observed sameAt positive guard

/-- Current public entry with a caller-supplied structural comparison. -/
def evaluateGuardWithSame [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (guard : Guard Formula) : Verdict := evaluate formulas solver observed sameAt true guard

/-- Current sparse entry uses the source root-shape comparison. -/
def evaluateGuardWithShape [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula) (guard : Guard Formula) : Verdict :=
  evaluateGuardWithSame formulas solver observed (sameShape formulas observed) guard

/-- Current complete entry compares the actual renamed subtrees. -/
def evaluateGuard [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (guard : Guard Formula) (term : Language.Term (Label Formula)) : Verdict :=
  evaluateGuardWithSame formulas solver (observe term) (sameTerm formulas term) guard

/-- Wrapping an atom in Not does not change any allocated name or ambiguous path. -/
theorem signed_tables [DecidableEq Formula] (formulas : Formulas Formula)
    (observed : Observations Formula) (sameAt : Path → Path → Option Bool)
    (positive : Bool) (guard : Guard Formula) :
    substitutionValues formulas observed sameAt (signed positive guard) =
      substitutionValues formulas observed sameAt guard := by
  cases positive <;> simp only [signed, Bool.false_eq_true, ↓reduceIte,
    substitutionValues, allocated, conflicts, values, actuals, actualPaths, usedNames, paths, requirements, ambiguous] <;> rfl

/-- The private helper uses the original atom table and pushed source polarity. -/
theorem scoped_eq [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) (guard : Guard Formula) :
    evaluateScoped formulas solver observed sameAt positive guard =
      let table := substitutionValues formulas observed (sameAt []) guard
      evaluateWith formulas solver observed sameAt table.1 table.2 [] positive guard := by
  unfold evaluateScoped SourceGuards.evaluateGuardWithSame
  rw [signed_tables]
  cases positive <;> simp [signed, evaluateWith]

/-- Outer conjunction uses the verdicts obtained by evaluating each operand independently. -/
theorem conjunction [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (parts : List (Guard Formula)) :
    evaluateGuardWithSame formulas solver observed sameAt (.and parts) =
      combine true (parts.map (evaluateGuardWithSame formulas solver observed sameAt)) := by
  change evaluate formulas solver observed sameAt true (.and parts) = _
  rw [evaluate]
  rfl

/-- Empty substitution is an identity, including around outer Boolean connectives. -/
theorem empty_scope [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) (guard : Guard Formula) :
    evaluate formulas solver observed sameAt positive (.substitute [] guard) =
      evaluate formulas solver observed sameAt positive guard := by simp only [evaluate]

/-- Confirmed intersection membership is the intersection of confirmed component membership. -/
theorem conjunction_yes [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (parts : List (Guard Formula)) :
    evaluateGuardWithSame formulas solver observed sameAt (.and parts) = .yes ↔
      ∀ guard ∈ parts, evaluateGuardWithSame formulas solver observed sameAt guard = .yes := by
  rw [conjunction, GuardConjunction.combine_yes]
  simp

/-- Flattening outer conjunctions preserves the current dispatcher in either polarity. -/
theorem atoms_evaluate [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) (guard : Guard Formula) :
    combine positive ((GuardConjunction.atoms guard).map (evaluate formulas solver observed sameAt positive)) =
      evaluate formulas solver observed sameAt positive guard := by
  let eval := evaluate formulas solver observed sameAt positive
  induction guard using SourceGuards.Guard.rec
    (motive_2 := fun guards => ∀ guard ∈ guards,
      combine positive ((GuardConjunction.atoms guard).map eval) = eval guard) with
  | top => cases positive <;> simp [GuardConjunction.atoms, evaluate, scoped_eq, evaluateWith, polarize, combine, negate]
  | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ | substitute _ _ _ | not _ _ | or _ _ =>
      simpa only [GuardConjunction.atoms, List.map_singleton] using GuardConjunction.combine_singleton positive _
  | and parts ih =>
      simp only [GuardConjunction.atoms, evaluate]
      change combine positive ((parts.flatMap GuardConjunction.atoms).map eval) = combine positive (parts.map eval)
      have same : parts.map (fun guard => combine positive ((GuardConjunction.atoms guard).map eval)) = parts.map eval := by
        apply List.map_congr_left
        exact ih
      have grouped := GuardConjunction.combine_flatMap positive (parts.map (fun guard => (GuardConjunction.atoms guard).map eval))
      simpa only [← List.flatMap_def, List.map_flatMap, List.map_map, Function.comp_def, same] using grouped
  | nil => rename_i guard member; simp at member
  | cons first rest ih ir =>
      rename_i guard member
      rcases List.mem_cons.mp member with rfl | member
      · exact ih
      · exact ir guard member

theorem conjoin_evaluate [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) (guards : List (Guard Formula)) :
    evaluate formulas solver observed sameAt positive (GuardConjunction.conjoin guards) =
      combine positive (guards.map (evaluate formulas solver observed sameAt positive)) := by
  cases guards with
  | nil => cases positive <;> simp [GuardConjunction.conjoin, evaluate, scoped_eq, evaluateWith, polarize, combine, negate]
  | cons first rest => cases rest with
    | nil => exact (GuardConjunction.combine_singleton positive _).symm
    | cons second rest => simp only [GuardConjunction.conjoin, evaluate]

/-- Current public conjunction normalization preserves all three verdicts without a solver renaming contract. -/
theorem normalize_evaluate [DecidableEq Formula] [DecidableEq (Guard Formula)]
    (le : Guard Formula → Guard Formula → Bool)
    (formulas : Formulas Formula) (solver : Entailment Formula) (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) (guard : Guard Formula) :
    evaluate formulas solver observed sameAt positive (GuardConjunction.normalize le guard) =
      evaluate formulas solver observed sameAt positive guard := by
  rw [GuardConjunction.normalize, conjoin_evaluate, ← atoms_evaluate formulas solver observed sameAt positive guard]
  apply GuardConjunction.combine_ext
  intro verdict
  simp [GuardConjunction.canonical_mem]

end MicroCFTA.SourceBooleanEntry
