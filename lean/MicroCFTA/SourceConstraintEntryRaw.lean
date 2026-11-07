import MicroCFTA.SourceCompactGuards

/-!
# Current constraint evaluation on public raw equality payloads

Constraint.equalities reads the stored field through the positive-guard
accessor. equalitiesHold checks that result. evaluateConstraint then checks
the complete guard. This predicate records its successful Boolean result.
It does not model IO demand or unknown/error effects.

The older SourceSymbolicIndex predicate checks the stored field directly.
ActiveOption suffices for agreement. Public raw constructors do not enforce
that condition. A singleton at an absent path gives a concrete difference
when a nonempty positive guard causes normalization to discard the singleton.
The Top fast path retains the stored singleton and rejects in both models.
These are model-boundary facts, not a native/reference runtime defect.
-/
namespace MicroCFTA.SourceConstraintEntryRaw
open Language SourceGuards SourceObservations SourceSymbolicIndex SymbolicDriver
open SourceCompactGuards

variable {Formula : Type}

/-- Current successful constraint evaluation reads the actual equality accessor. -/
noncomputable def acceptsConstraint [DecidableEq Formula] (formulas : Formulas Formula)
    (solver : Entailment Formula) (constraint : Constraint Formula)
    (term : Term (Label Formula)) : Bool :=
  ConstraintIndicators.equalityValue (classTest term) (sourceEqualities constraint) &&
    decide (SourceBooleanEntry.evaluateGuard formulas solver constraint.guard term = .yes)

/-- The Top accessor fast path retains every raw stored class. -/
theorem accepts_top [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (equalities : Option EqualityNormalize.Constraints) (term : Term (Label Formula)) :
    acceptsConstraint formulas solver ⟨equalities, .top⟩ term =
      SourceSymbolicIndex.acceptsConstraint formulas solver ⟨equalities, .top⟩ term := by
  rfl

/-- A residual guard also retains the raw stored field without normalization. -/
theorem accepts_residual [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (residual : positive constraint.guard = none)
    (term : Term (Label Formula)) :
    acceptsConstraint formulas solver constraint term =
      SourceSymbolicIndex.acceptsConstraint formulas solver constraint term := by
  have absent : positiveNormalized constraint.guard = none := by
    cases actual : positiveNormalized constraint.guard with
    | none => rfl
    | some equalities =>
        have supported := positiveNormalized_support constraint.guard
        rw [actual, residual] at supported
        cases supported
  simp only [acceptsConstraint, sourceEqualities, absent, SourceSymbolicIndex.acceptsConstraint]

/-- Existing normalized-field proofs remain valid for the current evaluator. -/
theorem accepts_of_active [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (active : ActiveOption constraint.equalities)
    (term : Term (Label Formula)) :
    acceptsConstraint formulas solver constraint term =
      SourceSymbolicIndex.acceptsConstraint formulas solver constraint term := by
  cases extracted : positive constraint.guard with
  | none => exact accepts_residual formulas solver constraint extracted term
  | some classes =>
      have positiveGuard : (positive constraint.guard).isSome = true := by rw [extracted]; rfl
      have exactValue := sourceEqualities_exact formulas solver constraint active positiveGuard term
      unfold acceptsConstraint
      rw [← exactValue]
      simp only [SourceSymbolicIndex.acceptsConstraint, Bool.and_assoc, Bool.and_self]

private theorem pair_prepared :
    EqualityNormalize.complete (EqualityNormalize.prepare [[[0], [1]]]) = [[[0], [1]]] := by
  cbv

private theorem singleton_pair_prepared :
    EqualityNormalize.complete (EqualityNormalize.prepare [[[2]], [[0], [1]]]) = [[[0], [1]]] := by
  cbv

private theorem pair_step :
    EqualityNormalize.congruenceStep [[[0], [1]]] = some [[[0], [1]]] := by
  cbv

private theorem normalized_pair :
    SourceCompactGuards.normalize [[[0], [1]]] = some [[[0], [1]]] := by
  unfold SourceCompactGuards.normalize
  rw [arrayNormalize_eq]
  unfold EqualityNormalize.mkEqConstraints EqualityTermination.normalizationBound EqualityTermination.saturationBound
  rw [pair_prepared, EqualityNormalize.fixMaybe, pair_step]
  rfl

private theorem normalized_singleton_pair :
    SourceCompactGuards.normalize [[[2]], [[0], [1]]] = some [[[0], [1]]] := by
  unfold SourceCompactGuards.normalize
  rw [arrayNormalize_eq]
  unfold EqualityNormalize.mkEqConstraints EqualityTermination.normalizationBound EqualityTermination.saturationBound
  rw [singleton_pair_prepared, EqualityNormalize.fixMaybe, pair_step]
  rfl

/-- The actual accessor normalizes away the missing-path singleton. -/
theorem raw_accessor :
    sourceEqualities (⟨some [[[2]]], .same [0] [1]⟩ : Constraint Formula) = some [[[0], [1]]] := by
  have extracted : positiveNormalized (.same [0] [1] : Guard Formula) = some (some [[[0], [1]]]) := by
    change some (SourceCompactGuards.normalize [[[0], [1]]]) = some (some [[[0], [1]]])
    rw [normalized_pair]
  unfold sourceEqualities
  rw [extracted]
  change SourceCompactGuards.normalize [[[2]], [[0], [1]]] = some [[[0], [1]]]
  exact normalized_singleton_pair

/-- The current evaluator accepts f(a,a), while the stored-field predicate rejects it. -/
theorem raw_singleton_same [DecidableEq Formula] (formulas : Formulas Formula)
    (solver : Entailment Formula) (symbol leaf : Label Formula) :
    let constraint : Constraint Formula := ⟨some [[[2]]], .same [0] [1]⟩
    let term : Term (Label Formula) := .node symbol [.node leaf [], .node leaf []]
    acceptsConstraint formulas solver constraint term = true ∧
      SourceSymbolicIndex.acceptsConstraint formulas solver constraint term = false := by
  let term : Term (Label Formula) := .node symbol [.node leaf [], .node leaf []]
  have guard : SourceBooleanEntry.evaluateGuard formulas solver (.same [0] [1]) term = .yes := by
    apply (positive_exact formulas solver (.same [0] [1]) [[[0], [1]]]
      (by simp [positive]) term).mpr
    simp [term, classTest, Symbolic.ClassSatisfied, Term.atPath]
  have source : acceptsConstraint formulas solver ⟨some [[[2]]], .same [0] [1]⟩ term = true := by
    unfold acceptsConstraint
    rw [raw_accessor]
    change (ConstraintIndicators.equalityValue (classTest term) (some [[[0], [1]]]) &&
      decide (SourceBooleanEntry.evaluateGuard formulas solver (.same [0] [1]) term = .yes)) = true
    rw [guard]
    simp [term, ConstraintIndicators.equalityValue, classTest, Symbolic.ClassSatisfied, Term.atPath]
  have stored : SourceSymbolicIndex.acceptsConstraint formulas solver
      ⟨some [[[2]]], .same [0] [1]⟩ term = false := by
    simp [SourceSymbolicIndex.acceptsConstraint, term, ConstraintIndicators.equalityValue,
      classTest, Symbolic.ClassSatisfied, Term.atPath]
  exact ⟨source, stored⟩

/-- Without the positive Same, both entries reject the absent raw singleton. -/
theorem raw_singleton_top [DecidableEq Formula] (formulas : Formulas Formula)
    (solver : Entailment Formula) (symbol leaf : Label Formula) :
    let constraint : Constraint Formula := ⟨some [[[2]]], .top⟩
    let term : Term (Label Formula) := .node symbol [.node leaf [], .node leaf []]
    acceptsConstraint formulas solver constraint term = false ∧
      SourceSymbolicIndex.acceptsConstraint formulas solver constraint term = false := by
  have stored : SourceSymbolicIndex.acceptsConstraint formulas solver ⟨some [[[2]]], .top⟩
      (.node symbol [.node leaf [], .node leaf []]) = false := by
    simp [SourceSymbolicIndex.acceptsConstraint, ConstraintIndicators.equalityValue,
      classTest, Symbolic.ClassSatisfied, Term.atPath]
  exact ⟨(accepts_top formulas solver _ _).trans stored, stored⟩

end MicroCFTA.SourceConstraintEntryRaw
