import MicroCFTA.SourceEqualityInheritedIteration
import MicroCFTA.SourceEqualityNormalizationInitial

/-!
# Original inherited carrier counterexamples

These statements use finite sequences of actual payload operations.
They do not assert that a complete worker admits these sequences.
-/
namespace MicroCFTA.SourceEqualityInheritedCarrierFailure
open EqualityNormalize SourceEqualityClassOrder
open SourceEqualityInheritedPayload SourceEqualityNormalizationCarrier

private def ownRaw : Constraints := [[[0], [1, 0, 0]]]
private def seedRaw : Constraints := [[[0, 0], [0, 1]]]
private def combinedRaw : Constraints :=
  [[[0], [1, 0, 0]], [[0, 0], [0, 1], [1, 0, 0, 0], [1, 0, 0, 1]]]
private def original : List Path := ownRaw.flatten ++ seedRaw.flatten
private def ownPayload := recordsOf ownRaw
private def seedPayload := recordsOf seedRaw
private def combinedPayload := recordsOf combinedRaw

private theorem read_own : SourceEqualityPhysicalPayload.read (some ownRaw) = .ok ownPayload := by
  cbv

private theorem read_seed : SourceEqualityPhysicalPayload.read (some seedRaw) = .ok seedPayload := by
  cbv

private theorem wellFormed_of_reference (raw : Constraints) (fuel : Nat)
    (payload : SourceEqualityPrecheck.Constraint)
    (normalized : mkEqConstraints fuel raw = .normalized raw)
    (read : SourceEqualityPhysicalPayload.read (some raw) = .ok payload) :
    SourceEqualityDescend.WellFormed payload := by
  apply read_wellFormed (some raw) ?_ payload read
  intro output same
  cases same
  exact SourceEqualityGuardReadback.normalized normalized

private theorem initial_common : Common 4 original [0, 1] (ownRaw ++ seedRaw) := by
  have included : ∀ path ∈ members (ownRaw ++ seedRaw), path ∈ original := by
    intro path member
    simpa [members, original] using member
  have common := SourceEqualityNormalizationInitial.prepare_common_of_original original included
  have gap : EqualityTrie.pathBudget original = 4 := by cbv
  have alphabet : original.flatten.eraseDups = [0, 1] := by cbv
  have prepared : prepare (ownRaw ++ seedRaw) = ownRaw ++ seedRaw := by cbv
  rw [gap, alphabet, prepared] at common
  exact common

private theorem not_anchored : ¬ EqualityTermination.Anchored original [[[0, 0, 0], [0, 0, 1]]] := by
  intro anchored
  obtain ⟨path, present, initial⟩ := anchored [[0, 0, 0], [0, 0, 1]] (by simp)
  have selected : path = [0, 0, 0] ∨ path = [0, 0, 1] := by simpa using present
  rcases selected with rfl | rfl <;> simp [original, ownRaw, seedRaw] at initial

/-- Actual combination and physical descent can lose all original class anchors. -/
theorem payload_anchor_loss :
    Common 4 [[0], [1, 0, 0], [0, 0], [0, 1]] [0, 1]
      [[[0], [1, 0, 0]], [[0, 0], [0, 1]]] ∧
    ∃ own inherited combined : SourceEqualityPrecheck.Constraint,
      SourceEqualityPhysicalPayload.read (some [[[0], [1, 0, 0]]]) = .ok own ∧
      SourceEqualityPhysicalPayload.read (some [[[0, 0], [0, 1]]]) = .ok inherited ∧
      SourceEqualityDescend.WellFormed own ∧ SourceEqualityDescend.WellFormed inherited ∧
      combine inherited own = .ok combined ∧
      classes (SourceEqualityDescend.descend combined 1) = some [[[0, 0, 0], [0, 0, 1]]] ∧
      ¬ EqualityTermination.Anchored [[0], [1, 0, 0], [0, 0], [0, 1]]
        [[[0, 0, 0], [0, 0, 1]]] := by
  refine ⟨initial_common, ownPayload, seedPayload, combinedPayload, read_own, read_seed, ?_, ?_, ?_, ?_, not_anchored⟩
  · exact wellFormed_of_reference ownRaw 1 ownPayload (by cbv) read_own
  · exact wellFormed_of_reference seedRaw 1 seedPayload (by cbv) read_seed
  · apply SourceEqualityInheritedIteration.combineReference_exact 4 seedPayload ownPayload (.ok combinedPayload)
    cbv
  · cbv

private def longRaw : Constraints :=
  [[List.replicate 20 0 ++ [0], List.replicate 20 0 ++ [1]]]

/-- Nineteen actual payload cycles leave the initial length-twenty word carrier. -/
theorem original_word_bound_escape :
    ∃ own inherited output : SourceEqualityPrecheck.Constraint,
      SourceEqualityPhysicalPayload.read (some [[[0], [1, 0, 0]]]) = .ok own ∧
      SourceEqualityPhysicalPayload.read (some [[[0, 0], [0, 1]]]) = .ok inherited ∧
      SourceEqualityDescend.WellFormed own ∧ SourceEqualityDescend.WellFormed inherited ∧
      SourceEqualityInheritedIteration.iterate 1 own 19 inherited = .ok output ∧
      ¬ EqualitySaturation.Within (EqualityTermination.words [0, 1] 20)
        ((classes output).getD []) := by
  refine ⟨ownPayload, seedPayload, recordsOf longRaw, read_own, read_seed, ?_, ?_, ?_, ?_⟩
  · exact wellFormed_of_reference ownRaw 1 ownPayload (by cbv) read_own
  · exact wellFormed_of_reference seedRaw 1 seedPayload (by cbv) read_seed
  · apply SourceEqualityInheritedIteration.reference_exact 4 1 ownPayload 19 seedPayload (.ok (recordsOf longRaw))
    cbv
  · have paths : classes (recordsOf longRaw) = some longRaw := by cbv
    rw [paths]
    change ¬ EqualitySaturation.Within (EqualityTermination.words [0, 1] 20) longRaw
    intro included
    let first : Path := List.replicate 20 0 ++ [0]
    have present : first ∈ members longRaw := by
      simp [members, longRaw, first]
    have short := ((EqualityTermination.words_correct [0, 1] 20 first).mp (included first present)).1
    have length : first.length = 21 := by cbv
    omega

end MicroCFTA.SourceEqualityInheritedCarrierFailure
