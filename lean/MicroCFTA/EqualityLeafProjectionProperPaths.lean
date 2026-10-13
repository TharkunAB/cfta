import MicroCFTA.EqualitySource

/-!
# Proper paths from completed source equality normalization

A nontrivial class containing the empty path also contains a distinct
strict extension. The source contradiction check rejects that class.
Successful normalization therefore supplies the proper forest paths used
by physical projection without a finite-model assumption.
-/
namespace MicroCFTA.EqualityLeafProjectionProperPaths
open EqualityNormalize

/-- Every path in an active contradiction-free class list is nonempty. -/
theorem active_proper (classes : Constraints) (active : Active classes) (consistent : isContradicting classes = false) :
    ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [] := by
  intro paths member path present same
  subst path
  obtain ⟨left, leftMember, right, rightMember, different⟩ := active paths member
  have allEmpty : ∀ other ∈ paths, other = [] := by
    intro other included
    apply Classical.byContradiction
    intro nonempty
    have contradiction : isContradicting classes = true := (isContradicting_correct classes).mpr
      ⟨paths, member, [], present, other, included, ⟨other, rfl⟩, Ne.symm nonempty⟩
    rw [consistent] at contradiction
    cases contradiction
  exact different ((allEmpty left leftMember).trans (allEmpty right rightMember).symm)

/-- Completed normalization derives proper paths directly from source invariants. -/
theorem normalized_proper (fuel : Nat) (input output : Constraints)
    (completed : mkEqConstraints fuel input = .normalized output) :
    ∀ paths ∈ output, ∀ path ∈ paths, path ≠ [] := by
  have invariants := mkEqConstraints_invariants fuel input output completed
  exact active_proper output invariants.1 invariants.2.1

/-- Reordering or filtering normalized classes preserves their proper paths. -/
theorem selected_proper (fuel : Nat) (input output selected : Constraints)
    (completed : mkEqConstraints fuel input = .normalized output)
    (members : ∀ paths ∈ selected, paths ∈ output) :
    ∀ paths ∈ selected, ∀ path ∈ paths, path ≠ [] :=
  fun paths member => normalized_proper fuel input output completed paths (members paths member)

/-- The executable source array normalizer supplies the same proper-path guarantee. -/
theorem array_eventual_proper (iterations : Nat) (input : Constraints) :
    ∃ bound, ∀ work, bound ≤ work → ∀ output,
      EqualityIndex.normalizeArray iterations work input = .normalized output →
        ∀ paths ∈ output, ∀ path ∈ paths, path ≠ [] := by
  obtain ⟨bound, agrees⟩ := EqualityIndex.normalizeArray_eventual iterations input
  refine ⟨bound, ?_⟩
  intro work enough output completed
  rw [agrees work enough] at completed
  exact normalized_proper iterations input output completed

end MicroCFTA.EqualityLeafProjectionProperPaths
