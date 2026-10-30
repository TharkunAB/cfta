import MicroCFTA.SourceEqualityNormalizationCarrier

/-!
# Path certificates from one original path list

Preparation removes empty and trivial classes before certificates are initialized.
The original path list determines the gap, anchors, and alphabet.
-/
namespace MicroCFTA.SourceEqualityNormalizationInitial
open EqualityNormalize EqualitySaturation EqualityTermination SourceCompactGuards
open SourceEqualityNormalizationCarrier

private theorem prepared_member_original {classes : Constraints} {path : EqualityNormalize.Path}
    (member : path ∈ members (prepare classes)) : path ∈ members classes := by
  obtain ⟨paths, present, atPath⟩ := (mem_members _ _).mp member
  obtain ⟨mapped, _⟩ := List.mem_filter.mp present
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp mapped
  exact (mem_members _ _).mpr ⟨original, originalMember, by simpa using atPath⟩

/-- Every prepared input uses certificates computed from the same original paths. -/
theorem prepare_common_of_original (original : List EqualityNormalize.Path)
    {classes : Constraints} (included : ∀ path ∈ members classes, path ∈ original) :
    Common (EqualityTrie.pathBudget original) original original.flatten.eraseDups (prepare classes) := by
  refine ⟨?_, ?_, ?_⟩
  · intro path member
    have bound := EqualityTrie.pathBudget_sufficient original path
      (included path (prepared_member_original member))
    exact .short (by simp)
      (by simpa only [List.length_nil, Nat.zero_add] using Nat.le_of_lt bound)
  · intro paths present
    obtain ⟨anchor, inClass, _, _, _⟩ := prepare_active classes paths present
    exact ⟨anchor, inClass,
      included anchor (prepared_member_original ((mem_members _ _).mpr ⟨paths, present, inClass⟩))⟩
  · intro path member index atIndex
    simp only [List.mem_eraseDups, List.mem_flatten]
    exact ⟨path, included path (prepared_member_original member), atIndex⟩

variable {gap : Nat} {anchors : List EqualityNormalize.Path} {alphabet : List Nat}

/-- Successful normalization needs the certificates only after actual preparation. -/
theorem normalize_prepared_carrier {classes output : Constraints}
    (common : Common gap anchors alphabet (prepare classes))
    (observed : normalize classes = some output) :
    Common gap anchors alphabet output ∧ NormalState output ∧ isContradicting output = false ∧
      Within (words alphabet (gap * (anchors.length + 1))) output := by
  unfold normalize at observed
  rw [arrayNormalize_eq] at observed
  cases done : mkEqConstraints (EqualityTermination.normalizationBound classes) classes with
  | timeout | contradiction => simp [done, SymbolicEqualityBridge.resultClasses] at observed
  | normalized result =>
      have same : result = output := by
        simpa [done, SymbolicEqualityBridge.resultClasses] using observed
      subst output
      have retained : Common gap anchors alphabet result :=
        fixMaybe_common (EqualityTermination.normalizationBound classes) (complete (prepare classes)) result
          (complete_active _ (prepare_active classes))
          (complete_common (prepare_active classes) common) done
      obtain ⟨outActive, consistent, _, fixed⟩ := mkEqConstraints_invariants _ _ _ done
      have normal := step_normal result result outActive fixed
      exact ⟨retained, normal, consistent,
        bounded_state gap anchors alphabet result normal consistent
          retained.1 retained.2.1 retained.2.2⟩

/-- Conjunction preserves the same prepared certificates without raw active-input gates. -/
theorem normalize_append_prepared_carrier {first second output : Constraints}
    (left : Common gap anchors alphabet (prepare first))
    (right : Common gap anchors alphabet (prepare second))
    (observed : normalize (first ++ second) = some output) :
    Common gap anchors alphabet output ∧ NormalState output ∧ isContradicting output = false ∧
      Within (words alphabet (gap * (anchors.length + 1))) output := by
  apply normalize_prepared_carrier ?_ observed
  simpa only [prepare, List.map_append, List.filter_append] using append_common left right

/-- One original path list gives a finite carrier for every successful initial normalization. -/
theorem normalize_original_carrier (original : List EqualityNormalize.Path)
    {classes output : Constraints} (included : ∀ path ∈ members classes, path ∈ original)
    (observed : normalize classes = some output) :
    Common (EqualityTrie.pathBudget original) original original.flatten.eraseDups output ∧
      NormalState output ∧ isContradicting output = false ∧
      Within (words original.flatten.eraseDups
        (EqualityTrie.pathBudget original * (original.length + 1))) output := by
  exact normalize_prepared_carrier (prepare_common_of_original original included) observed

end MicroCFTA.SourceEqualityNormalizationInitial
