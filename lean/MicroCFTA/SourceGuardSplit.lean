import MicroCFTA.SourceBooleanEntry

/-!
# Current source semantic and structural guard splitting

The source splits outer conjunctions only. A nonconjunctive guard containing
Same remains one residual. Substitution scopes and negations stay intact.
-/
namespace MicroCFTA.SourceGuardSplit
open SourceGuards GuardConjunction

mutual
/-- The source scans all nested scopes and Boolean parts for syntactic equality. -/
def containsSame : Guard Formula → Bool
  | .same _ _ => true
  | .substitute _ inner | .not inner => containsSame inner
  | .and parts | .or parts => containsAny parts
  | _ => false
termination_by guard => sizeOf guard

/-- The source list any fold visits each nested guard. -/
def containsAny : List (Guard Formula) → Bool
  | [] => false
  | first :: rest => containsSame first || containsAny rest
termination_by guards => sizeOf guards
end

/-- The actual source fold omits Top components. -/
def prepend : Guard Formula → List (Guard Formula) → List (Guard Formula)
  | .top, rest => rest
  | guard, rest => guard :: rest

mutual
/-- Current splitGuard, retaining every scoped structural residual. -/
def split (guard : Guard Formula) : Guard Formula × Guard Formula :=
  if !containsSame guard then (guard, .top)
  else match guard with
    | .and parts => let pair := separate parts; (conjoin pair.1, conjoin pair.2)
    | _ => (.top, guard)
termination_by sizeOf guard

/-- Source foldr separate with independent Top removal in each component. -/
def separate : List (Guard Formula) → List (Guard Formula) × List (Guard Formula)
  | [] => ([], [])
  | first :: rest =>
      let current := split first
      let later := separate rest
      (prepend current.1 later.1, prepend current.2 later.2)
termination_by parts => sizeOf parts
end

private theorem join_shuffle (positive : Bool) (a b c d : Guards.Verdict) :
    join positive (join positive a b) (join positive c d) =
      join positive (join positive a c) (join positive b d) := by
  cases positive <;> cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem top_identity (positive : Bool) (answer : Guards.Verdict) :
    join positive (if positive then .yes else .no) answer = answer ∧
      join positive answer (if positive then .yes else .no) = answer := by
  cases positive <;> cases answer <;> decide

private theorem top_evaluate [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula) (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) :
    SourceBooleanEntry.evaluate formulas solver observed sameAt positive .top =
      (if positive then .yes else .no) := by
  cases positive <;> simp [SourceBooleanEntry.evaluate, SourceBooleanEntry.scoped_eq, evaluateWith, polarize, Guards.negate]

private theorem prepend_evaluate [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula) (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) (guard : Guard Formula) (parts : List (Guard Formula)) :
    combine positive ((prepend guard parts).map (SourceBooleanEntry.evaluate formulas solver observed sameAt positive)) =
      join positive (SourceBooleanEntry.evaluate formulas solver observed sameAt positive guard)
        (combine positive (parts.map (SourceBooleanEntry.evaluate formulas solver observed sameAt positive))) := by
  cases guard <;> simp only [prepend, List.map_cons, combine_cons]
  rw [top_evaluate]
  exact (top_identity positive _).1.symm

/-- A guard without equality stays wholly in the semantic component. -/
theorem semantic_split (guard : Guard Formula) (semantic : containsSame guard = false) :
    split guard = (guard, .top) := by
  cases guard <;> simp only [split, semantic, Bool.not_false, ↓reduceIte]

private theorem contains_conjoin (parts : List (Guard Formula)) :
    containsSame (conjoin parts) = containsAny parts := by
  cases parts with
  | nil => simp [conjoin, containsSame, containsAny]
  | cons first rest => cases rest <;> simp [conjoin, containsSame, containsAny]

private theorem contains_prepend (guard : Guard Formula) (parts : List (Guard Formula)) :
    containsAny (prepend guard parts) = (containsSame guard || containsAny parts) := by
  cases guard <;> simp only [prepend, containsAny, containsSame, Bool.false_or]

mutual
/-- The emitted semantic guard contains no syntactic equality in any nested scope. -/
theorem semantic_clear (guard : Guard Formula) : containsSame (split guard).1 = false := by
  by_cases semantic : containsSame guard = false
  · rw [semantic_split guard semantic]
    exact semantic
  · have structural : containsSame guard = true := by cases found : containsSame guard <;> simp_all
    cases guard <;> simp only [split, structural, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    all_goals try (simp [containsSame] at structural)
    all_goals try exact (by simp [containsSame])
    rename_i parts
    rw [contains_conjoin]
    exact separate_clear parts
termination_by sizeOf guard

/-- The source fold places only equality-free guards in its semantic accumulator. -/
theorem separate_clear (parts : List (Guard Formula)) : containsAny (separate parts).1 = false := by
  cases parts with
  | nil => simp [separate, containsAny]
  | cons first rest => simp only [separate, contains_prepend, semantic_clear first, separate_clear rest, Bool.false_or]
termination_by sizeOf parts
end

mutual
/-- Splitting preserves the complete current three-valued evaluator in either polarity. -/
theorem split_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula) (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) (guard : Guard Formula) :
    join positive (SourceBooleanEntry.evaluate formulas solver observed sameAt positive (split guard).1)
      (SourceBooleanEntry.evaluate formulas solver observed sameAt positive (split guard).2) =
      SourceBooleanEntry.evaluate formulas solver observed sameAt positive guard := by
  by_cases semantic : containsSame guard = false
  · rw [semantic_split guard semantic]
    simp only [top_evaluate]
    exact (top_identity positive _).2
  · have structural : containsSame guard = true := by cases found : containsSame guard <;> simp_all
    cases guard <;> simp only [split, structural, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    all_goals try (rw [top_evaluate]; exact (top_identity positive _).1)
    rename_i parts
    simp only [SourceBooleanEntry.conjoin_evaluate, SourceBooleanEntry.evaluate]
    exact separate_exact formulas solver observed sameAt positive parts
termination_by sizeOf guard

/-- The two actual fold accumulators retain every conjunct with its original verdict. -/
theorem separate_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula) (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) (parts : List (Guard Formula)) :
    join positive
      (combine positive ((separate parts).1.map (SourceBooleanEntry.evaluate formulas solver observed sameAt positive)))
      (combine positive ((separate parts).2.map (SourceBooleanEntry.evaluate formulas solver observed sameAt positive))) =
      combine positive (parts.map (SourceBooleanEntry.evaluate formulas solver observed sameAt positive)) := by
  cases parts with
  | nil => cases positive <;> simp [separate, combine, join, Guards.conjunction, Guards.disjunction]
  | cons first rest =>
      simp only [separate, prepend_evaluate, List.map_cons, combine_cons]
      rw [join_shuffle, split_exact formulas solver observed sameAt positive first,
        separate_exact formulas solver observed sameAt positive rest]
termination_by sizeOf parts
end

/-- Confirmed membership requires both the semantic and retained structural part. -/
theorem split_yes [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (guard : Guard Formula) (term : Language.Term (SourceObservations.Label Formula)) :
    SourceBooleanEntry.evaluateGuard formulas solver guard term = .yes ↔
      SourceBooleanEntry.evaluateGuard formulas solver (split guard).1 term = .yes ∧
      SourceBooleanEntry.evaluateGuard formulas solver (split guard).2 term = .yes := by
  unfold SourceBooleanEntry.evaluateGuard SourceBooleanEntry.evaluateGuardWithSame
  rw [← split_exact formulas solver (SourceObservations.observe term) (SourceObservations.sameTerm formulas term) true guard]
  cases SourceBooleanEntry.evaluate formulas solver (SourceObservations.observe term) (SourceObservations.sameTerm formulas term) true (split guard).1 <;>
    cases SourceBooleanEntry.evaluate formulas solver (SourceObservations.observe term) (SourceObservations.sameTerm formulas term) true (split guard).2 <;> decide

end MicroCFTA.SourceGuardSplit
