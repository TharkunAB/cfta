import MicroCFTA.SourceEqualityNormalizationReceipt

/-!
# Exact fixed points of source equality normalization

A successful normalization result keeps its literal class and path order
when normalized again. Preparation and completion retain its canonical
representation. A one-step completed receipt proves the actual array result.
-/
namespace MicroCFTA.SourceCurrentEqualityNormalizationFixed
open EqualityNormalize

/-- A payload is fixed when actual source normalization returns the same ordered classes. -/
def Fixed (classes : Constraints) : Prop := SourceCompactGuards.normalize classes = some classes

private theorem successful (classes output : Constraints)
    (actual : SourceCompactGuards.normalize classes = some output) :
    mkEqConstraints (EqualityTermination.normalizationBound classes) classes = .normalized output := by
  unfold SourceCompactGuards.normalize at actual
  rw [SourceCompactGuards.arrayNormalize_eq] at actual
  cases result : mkEqConstraints (EqualityTermination.normalizationBound classes) classes with
  | timeout | contradiction => simp only [result,SymbolicEqualityBridge.resultClasses,reduceCtorEq] at actual
  | normalized values =>
      have same : values = output := by simpa only [result,SymbolicEqualityBridge.resultClasses,Option.some.injEq] using actual
      subst output
      exact result

private theorem eraseDups_fixed (paths : Class) (unique : paths.Nodup) : paths.eraseDups = paths := by
  induction paths with
  | nil => rfl
  | cons first rest ih =>
      have parts := List.nodup_cons.mp unique
      have kept : rest.filter (fun value => !value == first) = rest := by
        apply List.filter_eq_self.mpr
        intro value member
        have different : value ≠ first := by intro same; exact parts.1 (same ▸ member)
        simp only [Bool.not_eq_true,beq_eq_false_iff_ne]
        exact different
      rw [List.eraseDups_cons,kept,ih parts.2]

private theorem prepare_fixed (classes : Constraints) (normal : EqualitySaturation.NormalState classes) :
    prepare classes = classes := by
  have mapped : classes.map List.eraseDups = classes := by
    calc
      classes.map List.eraseDups = classes.map id := List.map_congr_left (by
        intro paths member
        exact eraseDups_fixed paths (by simpa only [normal.2.2.2 paths member] using canonicalClass_nodup paths))
      _ = classes := List.map_id
  unfold prepare
  rw [mapped]
  apply List.filter_eq_self.mpr
  intro paths member
  exact (nontrivialB_correct paths).mpr (normal.1 paths member)

private theorem canonicalize_fixed (classes : Constraints) (normal : EqualitySaturation.NormalState classes) :
    canonicalize classes = classes := by
  have mapped : classes.map canonicalClass = classes := by
    calc
      classes.map canonicalClass = classes.map id := List.map_congr_left normal.2.2.2
      _ = classes := List.map_id
  unfold canonicalize
  rw [mapped]
  apply List.mergeSort_of_pairwise
  simpa only [decide_eq_true_eq] using normal.2.2.1

private theorem complete_fixed (classes : Constraints) (normal : EqualitySaturation.NormalState classes) :
    complete classes = classes := by
  have stopped := (mergeOne_none classes).mpr normal.2.1
  have unchanged (fuel : Nat) : completeFuel fuel classes = classes := by
    cases fuel with
    | zero => rfl
    | succ fuel => simp only [completeFuel,stopped]
  unfold complete
  rw [unchanged]
  exact canonicalize_fixed classes normal

/-- Active classes at an exact executable congruence fixed point are fixed by the actual source normalizer. -/
theorem of_step (classes : Constraints) (active : Active classes)
    (step : congruenceStep classes = some classes) : Fixed classes := by
  have normal := EqualitySaturation.step_normal classes classes active step
  have one : mkEqConstraints 1 classes = .normalized classes := by
    simp only [mkEqConstraints,prepare_fixed classes normal,complete_fixed classes normal,fixMaybe,step,ite_true]
  have array := SourceEqualityNormalizationReceipt.array_eq 1 classes (by rw [one]; intro impossible; cases impossible)
  change SourceCompactGuards.normalize classes = some classes
  unfold SourceCompactGuards.normalize
  rw [array,one]
  rfl

/-- Every successful actual normalization produces an exact ordered normalization fixed point. -/
theorem normalize_idempotent (classes output : Constraints)
    (actual : SourceCompactGuards.normalize classes = some output) : Fixed output := by
  have invariant := mkEqConstraints_invariants _ classes output (successful classes output actual)
  exact of_step output invariant.1 invariant.2.2.2

/-- An actual fixed payload supplies all active, consistent, disjoint, and executable-step invariants. -/
theorem invariants (classes : Constraints) (fixed : Fixed classes) :
    Active classes ∧ isContradicting classes = false ∧
      classes.Pairwise (fun left right => overlap left right = false) ∧ congruenceStep classes = some classes :=
  mkEqConstraints_invariants _ classes classes (successful classes classes fixed)

/-- An empty prefix does not change actual normalization of a fixed payload. -/
theorem empty_append (classes : Constraints) (fixed : Fixed classes) :
    SourceCompactGuards.normalize ([] ++ classes) = some classes := by
  simpa only [List.nil_append] using fixed

/-- Actual source combination with an empty left payload retains the exact fixed payload. -/
theorem combine_empty_left (classes : Constraints) (fixed : Fixed classes) :
    SourceCompactGuards.combineEqualities (some []) (some classes) = some classes := by
  cases classes with
  | nil => rfl
  | cons first rest => simpa only [SourceCompactGuards.combineEqualities,List.nil_append] using fixed

/-- Actual source combination with an empty right payload retains the exact fixed payload. -/
theorem combine_empty_right (classes : Constraints) (fixed : Fixed classes) :
    SourceCompactGuards.combineEqualities (some classes) (some []) = some classes := by
  cases classes with
  | nil => rfl
  | cons first rest => simpa only [SourceCompactGuards.combineEqualities,List.append_nil] using fixed

end MicroCFTA.SourceCurrentEqualityNormalizationFixed
