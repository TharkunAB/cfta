import MicroCFTA.SymbolicAllocatedGraph
import MicroCFTA.EqualityNormalize

/-!
# Normalized path classes and symbolic indicators

PCS classes equate distinct paths. Symbolic classes require a common existing
subtree. These interpretations agree for nontrivial normalized classes.
Trivial PCS classes must be removed before compilation. A reflexive `Same`
guard still requires path existence and is not removed by this bridge.
-/
namespace MicroCFTA.SymbolicEqualityBridge
open Language EqualityNormalize SymbolicDriver
open Lattice (indicator)

/-- A common existing subtree satisfies every distinct pair in a class. -/
theorem common_implies_pcs (term : Term Symbol) (paths : Class)
    (common : Symbolic.ClassSatisfied term paths) : ClassSat term paths := by
  cases paths with
  | nil => intro left member; cases member
  | cons first rest =>
    obtain ⟨value, head, tail⟩ := common
    have all : ∀ path ∈ first :: rest, term.atPath path = some value := by
      intro path member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact tail path member
    intro left leftMember right rightMember _
    exact ⟨value, all left leftMember, all right rightMember⟩

/-- A nontrivial PCS class supplies one existing value at every path in that class. -/
theorem pcs_implies_common (term : Term Symbol) (paths : Class) (active : Nontrivial paths)
    (satisfied : ClassSat term paths) : Symbolic.ClassSatisfied term paths := by
  obtain ⟨left, leftMember, right, rightMember, different⟩ := active
  obtain ⟨value, leftValue, _⟩ := satisfied left leftMember right rightMember different
  have all : ∀ path ∈ paths, term.atPath path = some value := by
    intro path member
    by_cases same : left = path
    · simpa [← same] using leftValue
    · obtain ⟨other, atLeft, atPath⟩ := satisfied left leftMember path member same
      have equal : other = value := Option.some.inj (atLeft.symm.trans leftValue)
      simpa [equal] using atPath
  cases paths with
  | nil => trivial
  | cons first rest =>
    exact ⟨value, all first (by simp), fun path member => all path (by simp [member])⟩

/-- The source canonical-class invariant is sufficient for exact indicator interpretation. -/
theorem active_class_exact (term : Term Symbol) (paths : Class) (active : Nontrivial paths) :
    Symbolic.ClassSatisfied term paths ↔ ClassSat term paths :=
  ⟨common_implies_pcs term paths, pcs_implies_common term paths active⟩

/-- Compiled normalized PCS classes have exactly their independent equality denotation. -/
theorem active_classes_exact (term : Term Symbol) (classes : Constraints) (active : Active classes) :
    classes.all (classTest term) = true ↔ Satisfies term classes := by
  classical
  simp only [List.all_eq_true, classTest, decide_eq_true_eq, Satisfies]
  exact ⟨fun accepted paths member => (active_class_exact term paths (active paths member)).mp (accepted paths member),
    fun accepted paths member => (active_class_exact term paths (active paths member)).mpr (accepted paths member)⟩

/-- Read the equality indicator input of a completed source normalization result. -/
def resultClasses : RunResult → Option Constraints
  | .timeout | .contradiction => none
  | .normalized classes => some classes

/-- Every actual normalized output has nontrivial path classes. -/
def ActiveResult (result : RunResult) : Prop := ∀ classes, result = .normalized classes → Active classes

/-- The normalized equality test agrees with PCS semantics, including contradiction. -/
theorem result_value_exact (term : Term Symbol) (result : RunResult) (active : ActiveResult result) :
    ConstraintIndicators.equalityValue (classTest term) (resultClasses result) = true ↔ RunSat term result := by
  cases result with
  | timeout => simp [resultClasses, ConstraintIndicators.equalityValue, RunSat]
  | contradiction => simp [resultClasses, ConstraintIndicators.equalityValue, RunSat]
  | normalized classes =>
    exact active_classes_exact term classes (active classes rfl)

/-- A completed normalization preserves the symbolic indicator of already nontrivial input classes. -/
theorem normalization_score (term : Term Symbol) (fuel : Nat) (classes : Constraints)
    (active : Active classes) (finished : mkEqConstraints fuel classes ≠ .timeout) :
    ConstraintIndicators.score (classTest term)
      (ConstraintIndicators.equalityIndicators (resultClasses (mkEqConstraints fuel classes))) =
      indicator (classes.all (classTest term)) := by
  classical
  have outputActive : ActiveResult (mkEqConstraints fuel classes) :=
    fun output success => (mkEqConstraints_invariants fuel classes output success).1
  rw [ConstraintIndicators.equality_correct]
  congr 1
  apply Bool.eq_iff_iff.mpr
  exact (result_value_exact term _ outputActive).trans
    ((mkEqConstraints_correct term fuel classes finished).trans (active_classes_exact term classes active).symm)

/-- Normalizing the conjunction of two canonical equality inputs multiplies their indicators. -/
theorem combined_equality_score (term : Term Symbol) (fuel : Nat) (left right : Constraints)
    (leftActive : Active left) (rightActive : Active right)
    (finished : mkEqConstraints fuel (left ++ right) ≠ .timeout) :
    ConstraintIndicators.score (classTest term)
      (ConstraintIndicators.equalityIndicators (resultClasses (mkEqConstraints fuel (left ++ right)))) =
      ConstraintIndicators.score (classTest term) (ConstraintIndicators.equalityIndicators (some left)) *
        ConstraintIndicators.score (classTest term) (ConstraintIndicators.equalityIndicators (some right)) := by
  have combinedActive : Active (left ++ right) := by
    intro paths member
    rcases List.mem_append.mp member with member | member
    · exact leftActive paths member
    · exact rightActive paths member
  rw [normalization_score term fuel (left ++ right) combinedActive finished,
    List.all_append, Lattice.indicator_and, ConstraintIndicators.equality_correct, ConstraintIndicators.equality_correct]
  rfl

/-- The source guard conjunction removes truth and repeated identical operands. -/
def combineGuards [DecidableEq (ConstraintIndicators.Guard Atom Residual)] :
    ConstraintIndicators.Guard Atom Residual → ConstraintIndicators.Guard Atom Residual →
      ConstraintIndicators.Guard Atom Residual
  | .top, right => right
  | left, .top => left
  | left, right => if left = right then left else .and [left, right]

/-- The source guard simplification retains exact Boolean conjunction. -/
theorem combineGuards_exact [DecidableEq (ConstraintIndicators.Guard Atom Residual)]
    (test : Atom → Bool) (residual : Residual → Bool)
    (left right : ConstraintIndicators.Guard Atom Residual) :
    ConstraintIndicators.eval test residual (combineGuards left right) =
      (ConstraintIndicators.eval test residual left && ConstraintIndicators.eval test residual right) := by
  cases left <;> cases right <;>
    simp [combineGuards, ConstraintIndicators.eval, ConstraintIndicators.all] <;>
    split <;> simp_all [ConstraintIndicators.eval, ConstraintIndicators.all]

/-- Completed path-class normalization preserves the complete Boolean equality test. -/
theorem normalization_value (term : Term Symbol) (fuel : Nat) (classes : Constraints)
    (active : Active classes) (finished : mkEqConstraints fuel classes ≠ .timeout) :
    ConstraintIndicators.equalityValue (classTest term) (resultClasses (mkEqConstraints fuel classes)) =
      classes.all (classTest term) := by
  apply Bool.eq_iff_iff.mpr
  exact (result_value_exact term _
    (fun output success => (mkEqConstraints_invariants fuel classes output success).1)).trans
    ((mkEqConstraints_correct term fuel classes finished).trans (active_classes_exact term classes active).symm)

/-- Recompiling the source normalized conjunction has the exact raw indicator product. -/
theorem conjoined_constraint_score [DecidableEq (ConstraintIndicators.Guard Class Residual)]
    (term : Term Symbol) (residual : Residual → Bool) (fuel : Nat) (left right : Constraints)
    (leftActive : Active left) (rightActive : Active right)
    (finished : mkEqConstraints fuel (left ++ right) ≠ .timeout)
    (leftGuard rightGuard : ConstraintIndicators.Guard Class Residual)
    (leftSeries rightSeries outputSeries : ConstraintIndicators.Series Class)
    (leftCompiled : ConstraintIndicators.constraintIndicators (some left) leftGuard = .ok leftSeries)
    (rightCompiled : ConstraintIndicators.constraintIndicators (some right) rightGuard = .ok rightSeries)
    (outputCompiled : ConstraintIndicators.constraintIndicators (resultClasses (mkEqConstraints fuel (left ++ right)))
      (combineGuards leftGuard rightGuard) = .ok outputSeries) :
    ConstraintIndicators.score (classTest term) outputSeries =
      ConstraintIndicators.score (classTest term) leftSeries * ConstraintIndicators.score (classTest term) rightSeries := by
  have active : Active (left ++ right) := by
    intro paths member
    rcases List.mem_append.mp member with member | member
    · exact leftActive paths member
    · exact rightActive paths member
  rw [ConstraintIndicators.constraint_correct (classTest term) residual _ _ _ outputCompiled,
    ConstraintIndicators.constraint_correct (classTest term) residual _ _ _ leftCompiled,
    ConstraintIndicators.constraint_correct (classTest term) residual _ _ _ rightCompiled,
    combineGuards_exact, normalization_value term fuel (left ++ right) active finished,
    List.all_append, ← Lattice.indicator_and]
  simp only [ConstraintIndicators.equalityValue]
  congr 1
  exact Bool.and_left_comm .. |>.trans (by simp [Bool.and_assoc, Bool.and_left_comm])

end MicroCFTA.SymbolicEqualityBridge
