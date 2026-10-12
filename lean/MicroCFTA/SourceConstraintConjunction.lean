import MicroCFTA.SourceBooleanEntry
import MicroCFTA.EnumerationEquality

/-!
# Current semantic guards in constructor intersection

The public Boolean dispatcher supplies the residual conjunction law.
The equality normalizer supplies the independent path-equality law.
Together they derive the concrete product guard used by enumeration.
-/
namespace MicroCFTA.SourceConstraintConjunction
open SourceGuards SourceObservations EnumerationCorrectness EqualityNormalize

/-- A complete current guard contributes exactly its confirmed terms. -/
def meaning [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (guard : Guard Formula) (term : Language.Term (Label Formula)) : Prop :=
  SourceBooleanEntry.evaluateGuard formulas solver guard term = .yes

/-- Canonical conjunction has the independently evaluated meaning of both operands. -/
theorem merge_exact [DecidableEq Formula] [DecidableEq (Guard Formula)]
    (le : Guard Formula → Guard Formula → Bool)
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (left right : Guard Formula) (term : Language.Term (Label Formula)) :
    meaning formulas solver (GuardConjunction.merge le left right) term ↔
      meaning formulas solver left term ∧ meaning formulas solver right term := by
  unfold meaning SourceBooleanEntry.evaluateGuard SourceBooleanEntry.evaluateGuardWithSame
  rw [GuardConjunction.merge, SourceBooleanEntry.normalize_evaluate]
  have exact := SourceBooleanEntry.conjunction_yes formulas solver (observe term) (sameTerm formulas term) [left, right]
  simpa [SourceBooleanEntry.evaluateGuardWithSame] using exact

/-- The absence of a residual guard is the current Top guard. -/
theorem default_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (residual : Option (Guard Formula)) (term : Language.Term (Label Formula)) :
    meaning formulas solver (residual.getD .top) term ↔ ResidualHolds (meaning formulas solver) residual term := by
  cases residual with
  | some guard => rfl
  | none =>
      simp [meaning, SourceBooleanEntry.evaluateGuard, SourceBooleanEntry.evaluateGuardWithSame,
        SourceBooleanEntry.evaluate, SourceBooleanEntry.scoped_eq, evaluateWith, polarize, ResidualHolds]

/-- The source canonical guard conjunction discharges the residual product premise. -/
theorem residual_exact [DecidableEq Formula] [DecidableEq (Guard Formula)]
    (le : Guard Formula → Guard Formula → Bool)
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (left right : Option (Guard Formula)) (term : Language.Term (Label Formula)) :
    ResidualHolds (meaning formulas solver)
      (some (GuardConjunction.merge le (left.getD .top) (right.getD .top))) term ↔
      ResidualHolds (meaning formulas solver) left term ∧ ResidualHolds (meaning formulas solver) right term := by
  simp only [ResidualHolds]
  exact (merge_exact le formulas solver _ _ term).trans
    (and_congr (default_exact formulas solver left term) (default_exact formulas solver right term))

/-- Normalized equality classes and current semantic guards form the exact constructor product. -/
theorem edgeView_conjoin [DecidableEq Formula] [DecidableEq (Guard Formula)]
    (le : Guard Formula → Guard Formula → Bool)
    (formulas : Formulas Formula) (solver : Entailment Formula) (meet : Nat → Nat → Nat)
    (first second : EnumerationState.Edge (Label Formula) (Guard Formula)) (fuel : Nat)
    (leftActive : ∀ trie ∈ first.equalities, Nontrivial (EqualityTrie.fromPathTrie trie))
    (rightActive : ∀ trie ∈ second.equalities, Nontrivial (EqualityTrie.fromPathTrie trie))
    (output : Constraints)
    (success : mkEqConstraints fuel ((first.equalities ++ second.equalities).map EqualityTrie.fromPathTrie) = .normalized output) :
    EnumerationLanguage.edgeView (meaning formulas solver)
      ⟨first.symbol, (first.children.zip second.children).map (fun pair => meet pair.1 pair.2),
        EnumerationEquality.readClasses output,
        some (GuardConjunction.merge le (first.residual.getD .top) (second.residual.getD .top))⟩ =
      EnumerationIntersection.joinedEdge meet (EnumerationLanguage.edgeView (meaning formulas solver) first)
        (EnumerationLanguage.edgeView (meaning formulas solver) second) := by
  exact EnumerationEquality.edgeView_conjoin (meaning formulas solver) meet first second fuel
    leftActive rightActive output success _ (residual_exact le formulas solver _ _)

end MicroCFTA.SourceConstraintConjunction
