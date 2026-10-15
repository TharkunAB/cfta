import MicroCFTA.SourceEqualityPCSGuard

/-!
# Concrete source constructors at independent PCS semantics

Actual source normalization preserves raw PCS denotation. Complete constraint
conjunction therefore has a global law at this independent meaning. Public
indicator agreement still requires normalized source storage.
-/
namespace MicroCFTA.SourceEqualityPCSConstructors
open Language SourceObservations SourceGuards SourceSymbolicIndex SourceCompactGuards
open SourceEqualityGuardReadback SourceEqualityPCSGuard

/-- The actual source Top constructor accepts every finite term in independent PCS semantics. -/
theorem top_true [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula) (term : Term (Label Formula)) :
    holds formulas solver SourceEqualityConstraintConstructors.top term = true := by
  rw [public_eq formulas solver _ (active SourceEqualityConstraintConstructors.top_cached) term]
  exact SourceEqualityConstraintConstructors.top_true formulas solver term

/-- Literal source conjoinConstraints has complete independent conjunction semantics on all raw payloads. -/
theorem conjoined [DecidableEq Formula] [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (formulas : Formulas Formula) (solver : Entailment Formula) (first second : Constraint Formula) (term : Term (Label Formula)) :
    holds formulas solver (SourceEqualityConstraintConstructors.conjoin le first second) term =
      (holds formulas solver first term && holds formulas solver second term) := by
  apply Bool.eq_iff_iff.mpr
  simp only [holds_exact, Bool.and_eq_true_iff]
  change (Sat term (combineEqualities first.equalities second.equalities) ∧
    SourceBooleanEntry.evaluateGuard formulas solver (GuardConjunction.merge le first.guard second.guard) term = .yes) ↔ _
  rw [combine_sat]
  have guards := SourceConstraintConjunction.merge_exact le formulas solver first.guard second.guard term
  simp only [SourceConstraintConjunction.meaning] at guards
  rw [guards]
  exact ⟨fun ⟨⟨firstEq, secondEq⟩, firstGuard, secondGuard⟩ => ⟨⟨firstEq, firstGuard⟩, secondEq, secondGuard⟩,
    fun ⟨⟨firstEq, firstGuard⟩, secondEq, secondGuard⟩ => ⟨⟨firstEq, secondEq⟩, firstGuard, secondGuard⟩⟩

/-- The actual source plain predicate supplies global truth in independent PCS semantics. -/
theorem plain_true (formulas : Formulas FullSyntax.Formula) (solver : Entailment FullSyntax.Formula)
    (constraint : Constraint FullSyntax.Formula) (plain : SourceMemoGate.plain constraint = true) (term : Term (Label FullSyntax.Formula)) :
    holds formulas solver constraint term = true := by
  have tests := Bool.and_eq_true_iff.mp plain
  have empty : sourceEqualities constraint = some [] := of_decide_eq_true tests.1
  have supported : (positive constraint.guard).isSome = true := (positiveNormalized_support constraint.guard).symm.trans tests.2
  apply (positive_source formulas solver constraint supported term).mpr
  simp only [empty, Sat, EqualityNormalize.Satisfies, List.not_mem_nil, false_implies, implies_true]

end MicroCFTA.SourceEqualityPCSConstructors
