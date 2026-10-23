import MicroCFTA.SourceEqualityGuardReadback
import MicroCFTA.SourceConstraintConjunction
import MicroCFTA.SourceMemoGate

/-!
# Concrete source constraint constructors on normalized payloads

Source conjunction combines the stored equalities and canonical outer guards.
Its independent conjunction law requires the normalized payload invariant.
The actual plain test and Top constructor supply their local truth laws.
-/
namespace MicroCFTA.SourceEqualityConstraintConstructors
open Language SourceObservations SourceGuards SourceSymbolicIndex SourceCompactGuards
open SourceEqualityGuardReadback

/-- The source equality-free Top transition constraint. -/
def top : Constraint Formula := ⟨some [], .top⟩

/-- Actual conjoinConstraints combines stored equalities and canonical source guard conjunction. -/
noncomputable def conjoin [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (first second : Constraint Formula) : Constraint Formula :=
  ⟨combineEqualities first.equalities second.equalities, GuardConjunction.merge le first.guard second.guard⟩

/-- Top retains the physical cached-payload invariant. -/
theorem top_cached : Cached (top (Formula := Formula)).equalities := empty_cached

/-- Source conjunction derives the cached representation from its actual normalizer. -/
theorem conjoin_cached [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (first second : Constraint Formula) : Cached (conjoin le first second).equalities := combine_cached _ _

/-- Top accepts every complete term under the current public source evaluator. -/
theorem top_true [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula) (term : Term (Label Formula)) :
    acceptsConstraint formulas solver top term = true := by
  rw [sourceEqualities_exact formulas solver top (active top_cached) (by rfl) term]
  rfl

/-- Actual source conjunction has the exact Boolean language law on normalized stored operands. -/
theorem conjoined [DecidableEq Formula] [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (formulas : Formulas Formula) (solver : Entailment Formula) (first second : Constraint Formula)
    (firstActive : ActiveOption first.equalities) (secondActive : ActiveOption second.equalities) (term : Term (Label Formula)) :
    acceptsConstraint formulas solver (conjoin le first second) term =
      (acceptsConstraint formulas solver first term && acceptsConstraint formulas solver second term) := by
  have guards : decide (SourceBooleanEntry.evaluateGuard formulas solver (GuardConjunction.merge le first.guard second.guard) term = .yes) =
      (decide (SourceBooleanEntry.evaluateGuard formulas solver first.guard term = .yes) &&
        decide (SourceBooleanEntry.evaluateGuard formulas solver second.guard term = .yes)) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [Bool.and_eq_true_iff, decide_eq_true_eq, SourceConstraintConjunction.meaning] using
      SourceConstraintConjunction.merge_exact le formulas solver first.guard second.guard term
  change (ConstraintIndicators.equalityValue (SymbolicDriver.classTest term) (combineEqualities first.equalities second.equalities) &&
    decide (SourceBooleanEntry.evaluateGuard formulas solver (GuardConjunction.merge le first.guard second.guard) term = .yes)) =
      ((ConstraintIndicators.equalityValue (SymbolicDriver.classTest term) first.equalities &&
          decide (SourceBooleanEntry.evaluateGuard formulas solver first.guard term = .yes)) &&
        (ConstraintIndicators.equalityValue (SymbolicDriver.classTest term) second.equalities &&
          decide (SourceBooleanEntry.evaluateGuard formulas solver second.guard term = .yes)))
  rw [combine_value first.equalities second.equalities firstActive secondActive term, guards]
  simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

/-- The actual source plain test supplies truth from its accessor and syntax checks. -/
theorem plain_true (formulas : Formulas FullSyntax.Formula) (solver : Entailment FullSyntax.Formula)
    (constraint : Constraint FullSyntax.Formula) (stored : ActiveOption constraint.equalities)
    (plain : SourceMemoGate.plain constraint = true) (term : Term (Label FullSyntax.Formula)) :
    acceptsConstraint formulas solver constraint term = true := by
  have tests := Bool.and_eq_true_iff.mp plain
  have empty : sourceEqualities constraint = some [] := of_decide_eq_true tests.1
  have supported : (positive constraint.guard).isSome = true := (positiveNormalized_support constraint.guard).symm.trans tests.2
  rw [sourceEqualities_exact formulas solver constraint stored supported term, empty]
  rfl

/-- Singleton stored classes are outside the source invariant; normalization can discard their existence test. -/
theorem singleton_storage_boundary [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula) (symbol : Label Formula) :
    let malformed : Constraint Formula := ⟨some [[[0]]], .top⟩
    acceptsConstraint formulas solver malformed (.node symbol []) = false ∧
      combineEqualities malformed.equalities (some []) = some [] := by
  constructor
  · simp [acceptsConstraint, ConstraintIndicators.equalityValue, SymbolicDriver.classTest,
      Symbolic.ClassSatisfied, Language.Term.atPath]
  · change normalize ([[[0]]] ++ []) = some []
    unfold normalize
    rw [arrayNormalize_eq]
    cbv

end MicroCFTA.SourceEqualityConstraintConstructors
