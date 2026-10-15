import MicroCFTA.SourceCompactGuards

/-!
# Actual source equality accessor at arbitrary guards

The cached source classes come from completed normalization. The actual
accessor retains this representation. Acceptance of the complete constraint
implies its equality payload, including guards with a residual.
-/
namespace MicroCFTA.SourceEqualityGuardReadback
open Language EqualityNormalize SourceObservations SourceGuards SourceSymbolicIndex
open SourceCompactGuards

/-- A completed source payload has nontrivial, consistent, canonical classes. -/
def NormalClasses (classes : Constraints) : Prop :=
  Active classes ∧ isContradicting classes = false ∧
    ∀ paths ∈ classes, canonicalClass paths = paths

/-- Cached source equalities retain their actual normalized representation. -/
def Cached (equalities : Option Constraints) : Prop :=
  ∀ classes, equalities = some classes → NormalClasses classes

/-- Completed normalization supplies every physical source class invariant. -/
theorem normalized {fuel : Nat} {input output : Constraints}
    (done : mkEqConstraints fuel input = .normalized output) : NormalClasses output := by
  obtain ⟨active, consistent, _, fixed⟩ := mkEqConstraints_invariants _ _ _ done
  exact ⟨active, consistent, (EqualitySaturation.step_normal output output active fixed).2.2.2⟩

/-- Actual completed parent-array normalization derives the cached representation. -/
theorem normalize_cached (classes : Constraints) : Cached (normalize classes) := by
  intro output same
  unfold normalize at same
  rw [arrayNormalize_eq] at same
  cases done : mkEqConstraints (EqualityTermination.normalizationBound classes) classes with
  | timeout | contradiction => simp [done, SymbolicEqualityBridge.resultClasses] at same
  | normalized result =>
      have identical : result = output := by simpa [done, SymbolicEqualityBridge.resultClasses] using same
      subst output
      exact normalized done

/-- The empty source payload satisfies the same physical invariants. -/
theorem empty_cached : Cached (some []) := by
  intro classes same
  cases same
  simp [NormalClasses, Active, isContradicting]

/-- Actual source combination derives normalized classes, including its empty shortcut. -/
theorem combine_cached (first second : Option Constraints) : Cached (combineEqualities first second) := by
  cases first with
  | none => simp [combineEqualities, Cached]
  | some first => cases second with
    | none => simp [combineEqualities, Cached]
    | some second => cases first <;> cases second <;>
        first | exact empty_cached | exact normalize_cached _

/-- Constraint.equalities retains normalized physical payloads through every guard branch. -/
theorem source_cached (constraint : Constraint Formula) (cached : Cached constraint.equalities) :
    Cached (sourceEqualities constraint) := by
  unfold sourceEqualities
  split <;> first | exact cached | exact combine_cached _ _

/-- Cached class invariants imply the existing source indicator invariant. -/
theorem active {equalities : Option Constraints} (cached : Cached equalities) : ActiveOption equalities :=
  fun classes same => (cached classes same).1

/-- Acceptance of a complete source constraint implies its actual equality accessor result. -/
theorem accepted_equalities [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (stored : ActiveOption constraint.equalities)
    (term : Term (Label Formula)) (accepted : acceptsConstraint formulas solver constraint term = true) :
    ConstraintIndicators.equalityValue (SymbolicDriver.classTest term) (sourceEqualities constraint) = true := by
  by_cases positiveGuard : (positive constraint.guard).isSome = true
  · rwa [sourceEqualities_exact formulas solver constraint stored positiveGuard term] at accepted
  · have missing : positiveNormalized constraint.guard = none := by
      cases found : positiveNormalized constraint.guard with
      | none => rfl
      | some result =>
          have support := positiveNormalized_support constraint.guard
          rw [found] at support
          exact False.elim (positiveGuard support.symm)
    have storedAccepted : ConstraintIndicators.equalityValue (SymbolicDriver.classTest term) constraint.equalities = true := by
      exact (Bool.and_eq_true_iff.mp accepted).1
    simpa only [sourceEqualities, missing] using storedAccepted

/-- The physical equality payload denotes independent existing-path equality classes. -/
def Sat (term : Term Symbol) : Option Constraints → Prop
  | none => False
  | some classes => Satisfies term classes

/-- Actual equality indicators and independent payload satisfaction agree on source classes. -/
theorem value_exact [DecidableEq Symbol] (term : Term Symbol) (equalities : Option Constraints)
    (active : ActiveOption equalities) :
    ConstraintIndicators.equalityValue (SymbolicDriver.classTest term) equalities = true ↔ Sat term equalities := by
  cases equalities with
  | none => simp [ConstraintIndicators.equalityValue, Sat]
  | some classes => exact SymbolicEqualityBridge.active_classes_exact term classes (active classes rfl)

/-- Complete guard acceptance supplies actual own class satisfaction without a guard-to-payload premise. -/
theorem accepted_sat [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (stored : ActiveOption constraint.equalities)
    (term : Term (Label Formula)) (accepted : acceptsConstraint formulas solver constraint term = true) :
    Sat term (sourceEqualities constraint) :=
  (value_exact term _ (sourceEqualities_active constraint stored)).mp
    (accepted_equalities formulas solver constraint stored term accepted)

end MicroCFTA.SourceEqualityGuardReadback
