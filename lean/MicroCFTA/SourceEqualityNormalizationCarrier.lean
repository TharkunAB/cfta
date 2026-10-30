import MicroCFTA.SourceEqualityGuardReadback

/-!
# Common path bounds through actual source normalization

The gap, anchor list, and alphabet remain fixed across input conjunction.
Active input classes retain every recorded segmentation marker during preparation.
-/
namespace MicroCFTA.SourceEqualityNormalizationCarrier
open EqualityNormalize EqualitySaturation EqualityTermination SourceCompactGuards

/-- The three certificates use one fixed gap, anchor list, and alphabet. -/
def Common (gap : Nat) (anchors : List (List Nat)) (alphabet : List Nat)
    (classes : Constraints) : Prop :=
  SegmentedState gap classes ∧ Anchored anchors classes ∧ UsesAlphabet alphabet classes

variable {gap : Nat} {anchors : List (List Nat)} {alphabet : List Nat}

/-- Class-list concatenation preserves the same three certificates. -/
theorem append_common {first second : Constraints}
    (left : Common gap anchors alphabet first) (right : Common gap anchors alphabet second) :
    Common gap anchors alphabet (first ++ second) := by
  have leftIncluded : ∀ path ∈ members first, path ∈ members (first ++ second) := by
    intro path member
    obtain ⟨paths, present, atPath⟩ := (mem_members _ _).mp member
    exact (mem_members _ _).mpr ⟨paths, List.mem_append_left _ present, atPath⟩
  have rightIncluded : ∀ path ∈ members second, path ∈ members (first ++ second) := by
    intro path member
    obtain ⟨paths, present, atPath⟩ := (mem_members _ _).mp member
    exact (mem_members _ _).mpr ⟨paths, List.mem_append_right _ present, atPath⟩
  refine ⟨?_, ?_, ?_⟩
  · intro path member
    obtain ⟨paths, present, atPath⟩ := (mem_members _ _).mp member
    rcases List.mem_append.mp present with present | present
    · exact segments_mono gap first (first ++ second) leftIncluded [] path
        (left.1 path ((mem_members _ _).mpr ⟨paths, present, atPath⟩))
    · exact segments_mono gap second (first ++ second) rightIncluded [] path
        (right.1 path ((mem_members _ _).mpr ⟨paths, present, atPath⟩))
  · intro paths member
    rcases List.mem_append.mp member with member | member
    · exact left.2.1 paths member
    · exact right.2.1 paths member
  · intro path member
    obtain ⟨paths, present, atPath⟩ := (mem_members _ _).mp member
    rcases List.mem_append.mp present with present | present
    · exact left.2.2 path ((mem_members _ _).mpr ⟨paths, present, atPath⟩)
    · exact right.2.2 path ((mem_members _ _).mpr ⟨paths, present, atPath⟩)

private theorem prepare_members_active {classes : Constraints} (active : Active classes)
    (path : EqualityNormalize.Path) : path ∈ members (prepare classes) ↔ path ∈ members classes := by
  constructor
  · intro member
    obtain ⟨paths, present, atPath⟩ := (mem_members _ _).mp member
    obtain ⟨mapped, _⟩ := List.mem_filter.mp present
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp mapped
    exact (mem_members _ _).mpr ⟨original, originalMember, by simpa using atPath⟩
  · intro member
    obtain ⟨paths, present, atPath⟩ := (mem_members _ _).mp member
    have nontrivial : Nontrivial paths.eraseDups := by
      obtain ⟨left, inLeft, right, inRight, different⟩ := active paths present
      exact ⟨left, by simpa using inLeft, right, by simpa using inRight, different⟩
    apply (mem_members _ _).mpr
    exact ⟨paths.eraseDups,
      List.mem_filter.mpr ⟨List.mem_map.mpr ⟨paths, present, rfl⟩,
        (nontrivialB_correct _).mpr nontrivial⟩,
      by simpa using atPath⟩

/-- Active preparation retains the same recorded-path certificates. -/
theorem prepare_common {classes : Constraints} (active : Active classes)
    (common : Common gap anchors alphabet classes) :
    Common gap anchors alphabet (prepare classes) := by
  refine ⟨?_, ?_, ?_⟩
  · intro path member
    exact segments_mono gap classes (prepare classes)
      (fun path present => (prepare_members_active active path).mpr present) [] path
      (common.1 path ((prepare_members_active active path).mp member))
  · intro paths member
    obtain ⟨mapped, _⟩ := List.mem_filter.mp member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp mapped
    obtain ⟨anchor, inOriginal, anchored⟩ := common.2.1 original originalMember
    exact ⟨anchor, by simpa using inOriginal, anchored⟩
  · intro path member
    exact common.2.2 path ((prepare_members_active active path).mp member)

/-- Component completion retains the same certificates and does not split anchors. -/
theorem complete_common {classes : Constraints} (active : Active classes)
    (common : Common gap anchors alphabet classes) :
    Common gap anchors alphabet (complete classes) := by
  refine ⟨?_, ?_, ?_⟩
  · intro path member
    exact segments_mono gap classes (complete classes)
      (fun path present => (complete_members classes path).mpr present) [] path
      (common.1 path ((complete_members classes path).mp member))
  · intro component componentMember
    have normal := complete_normal classes active
    obtain ⟨path, present, _, _, _⟩ := normal.1 component componentMember
    have original : path ∈ members classes :=
      (complete_members classes path).mp ((mem_members _ _).mpr ⟨component, componentMember, present⟩)
    obtain ⟨source, sourceMember, inSource⟩ := (mem_members _ _).mp original
    obtain ⟨retained, retainedMember, included⟩ := complete_covers classes source sourceMember
    have same := components_equal (complete classes) normal.2.1 retained component
      retainedMember componentMember path (included path inSource) present
    obtain ⟨anchor, inOriginal, anchored⟩ := common.2.1 source sourceMember
    exact ⟨anchor, by simpa [same] using included anchor inOriginal, anchored⟩
  · intro path member
    exact common.2.2 path ((complete_members classes path).mp member)

/-- Actual successful fixed-point iteration retains the common certificates. -/
theorem fixMaybe_common (fuel : Nat) (classes output : Constraints)
    (active : Active classes) (common : Common gap anchors alphabet classes)
    (done : fixMaybe fuel classes = .normalized output) : Common gap anchors alphabet output := by
  induction fuel generalizing classes with
  | zero => simp [fixMaybe] at done
  | succ fuel ih =>
      cases stepped : congruenceStep classes with
      | none => simp [fixMaybe, stepped] at done
      | some next =>
          by_cases stable : next = classes
          · have same : output = classes := by simpa [fixMaybe, stepped, stable] using done.symm
            subst output
            exact common
          · have recursive : fixMaybe fuel next = .normalized output := by
              simpa [fixMaybe, stepped, stable] using done
            have nextCommon : Common gap anchors alphabet next :=
              ⟨step_segmented gap classes next common.1 stepped,
                step_anchored anchors classes next active common.2.1 stepped,
                step_alphabet alphabet classes next common.2.2 stepped⟩
            exact ih next (congruenceStep_invariants classes next active stepped).1 nextCommon recursive

/-- Actual successful source normalization retains the original three certificates. -/
theorem normalize_common {classes output : Constraints} (active : Active classes)
    (common : Common gap anchors alphabet classes)
    (observed : normalize classes = some output) :
    Common gap anchors alphabet output ∧ NormalState output ∧ isContradicting output = false := by
  unfold normalize at observed
  rw [arrayNormalize_eq] at observed
  cases done : mkEqConstraints (EqualityTermination.normalizationBound classes) classes with
  | timeout | contradiction => simp [done, SymbolicEqualityBridge.resultClasses] at observed
  | normalized result =>
      have same : result = output := by
        simpa [done, SymbolicEqualityBridge.resultClasses] using observed
      subst output
      have preserved : Common gap anchors alphabet result :=
        fixMaybe_common (EqualityTermination.normalizationBound classes) (complete (prepare classes)) result
          (complete_active _ (prepare_active classes))
          (complete_common (prepare_active classes) (prepare_common active common)) done
      obtain ⟨outActive, consistent, _, fixed⟩ := mkEqConstraints_invariants _ _ _ done
      exact ⟨preserved, step_normal result result outActive fixed, consistent⟩

/-- Successful input conjunction uses one finite carrier from the original certificates. -/
theorem normalize_append_carrier {first second output : Constraints}
    (firstActive : Active first) (secondActive : Active second)
    (left : Common gap anchors alphabet first) (right : Common gap anchors alphabet second)
    (observed : normalize (first ++ second) = some output) :
    Common gap anchors alphabet output ∧ NormalState output ∧ isContradicting output = false ∧
      Within (words alphabet (gap * (anchors.length + 1))) output := by
  have active : Active (first ++ second) := by
    intro paths member
    rcases List.mem_append.mp member with member | member
    · exact firstActive paths member
    · exact secondActive paths member
  have result := normalize_common active (append_common left right) observed
  exact ⟨result.1, result.2.1, result.2.2,
    bounded_state gap anchors alphabet output result.2.1 result.2.2
      result.1.1 result.1.2.1 result.1.2.2⟩

end MicroCFTA.SourceEqualityNormalizationCarrier
