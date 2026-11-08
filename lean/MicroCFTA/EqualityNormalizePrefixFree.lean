import MicroCFTA.SourceCompactGuards

/-!
# Normalization preserves globally prefix-free endpoints

Preparation removes paths. Component completion preserves path membership.
Global prefix freedom prevents every suffix-generation request. These facts
apply through the actual fixed-point loop and source array readback.

The premise ranges over all input classes together. Separate prefix freedom
for each class does not suffice. Later inherited conjunctions need the same
global premise for their complete combined input.
-/
namespace MicroCFTA.EqualityNormalizePrefixFree
open EqualityNormalize

private theorem prepared_member_original (classes : Constraints) (path : Path)
    (member : path ∈ members (prepare classes)) : path ∈ members classes := by
  obtain ⟨paths, present, atPath⟩ := (mem_members _ _).mp member
  obtain ⟨mapped, _⟩ := List.mem_filter.mp present
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp mapped
  exact (mem_members _ _).mpr ⟨original, originalMember, by simpa using atPath⟩

private theorem step_member_original (classes output : Constraints)
    (prefixFree : ∀ first ∈ members classes, ∀ second ∈ members classes,
      first.IsPrefix second → first = second)
    (done : congruenceStep classes = some output) (path : Path)
    (member : path ∈ members output) : path ∈ members classes := by
  have closed : complete (addCongruences classes) = output := by
    dsimp only [congruenceStep] at done
    split at done
    · cases done
    · exact Option.some.inj done
  rw [← closed] at member
  have added := (complete_members (addCongruences classes) path).mp member
  obtain ⟨paths, present, atPath⟩ := (mem_members _ _).mp added
  rcases List.mem_append.mp present with original | generated
  · exact (mem_members _ _).mpr ⟨paths, original, atPath⟩
  · obtain ⟨source, sourceMember, built⟩ := List.mem_flatMap.mp generated
    obtain ⟨suffix, suffixMember, _⟩ := List.mem_map.mp built
    obtain ⟨base, baseMember, extension, extensionMember, nonempty, equal⟩ :=
      (mem_suffixes _ _ _).mp suffixMember
    have baseOriginal : base ∈ members classes :=
      (mem_members _ _).mpr ⟨source, sourceMember, baseMember⟩
    have identical := prefixFree base baseOriginal extension extensionMember ⟨suffix, equal⟩
    have lengths := congrArg List.length equal
    have sameLength := congrArg List.length identical
    have empty : suffix = [] := List.length_eq_zero_iff.mp (by
      simp only [List.length_append] at lengths
      omega)
    exact False.elim (nonempty empty)

private theorem fixMaybe_member_original (fuel : Nat) (classes output : Constraints)
    (prefixFree : ∀ first ∈ members classes, ∀ second ∈ members classes,
      first.IsPrefix second → first = second)
    (done : fixMaybe fuel classes = .normalized output) (path : Path)
    (member : path ∈ members output) : path ∈ members classes := by
  induction fuel generalizing classes with
  | zero => cases done
  | succ fuel ih =>
      cases stepped : congruenceStep classes with
      | none => simp only [fixMaybe, stepped, reduceCtorEq] at done
      | some next =>
          by_cases stable : next = classes
          · have same : output = classes := by
              simpa only [fixMaybe, stepped, stable, ↓reduceIte,
                RunResult.normalized.injEq] using done.symm
            subst output
            exact member
          · have recursive : fixMaybe fuel next = .normalized output := by
              simpa only [fixMaybe, stepped, stable, ↓reduceIte] using done
            have included := step_member_original classes next prefixFree stepped
            have nextPrefixFree : ∀ first ∈ members next, ∀ second ∈ members next,
                first.IsPrefix second → first = second := by
              intro first firstMember second secondMember initial
              exact prefixFree first (included first firstMember)
                second (included second secondMember) initial
            exact included path (ih next nextPrefixFree recursive)

/-- A successful bounded reference normalization adds no globally prefix-free input endpoint. -/
theorem mkEqConstraints_mem_original (fuel : Nat) (classes output : Constraints)
    (prefixFree : ∀ first ∈ members classes, ∀ second ∈ members classes,
      first.IsPrefix second → first = second)
    (done : mkEqConstraints fuel classes = .normalized output) (path : Path)
    (member : path ∈ members output) : path ∈ members classes := by
  have included : ∀ original ∈ members (complete (prepare classes)), original ∈ members classes := by
    intro original present
    exact prepared_member_original classes original
      ((complete_members (prepare classes) original).mp present)
  have preparedPrefixFree : ∀ first ∈ members (complete (prepare classes)),
      ∀ second ∈ members (complete (prepare classes)), first.IsPrefix second → first = second := by
    intro first firstMember second secondMember initial
    exact prefixFree first (included first firstMember) second (included second secondMember) initial
  exact included path (fixMaybe_member_original fuel (complete (prepare classes)) output
    preparedPrefixFree done path member)

/-- Successful actual source normalization retains only original globally prefix-free endpoints. -/
theorem normalize_mem_original (classes output : Constraints)
    (prefixFree : ∀ first ∈ members classes, ∀ second ∈ members classes,
      first.IsPrefix second → first = second)
    (done : SourceCompactGuards.normalize classes = some output) (path : Path)
    (member : path ∈ members output) : path ∈ members classes := by
  unfold SourceCompactGuards.normalize at done
  rw [SourceCompactGuards.arrayNormalize_eq] at done
  cases actual : mkEqConstraints (EqualityTermination.normalizationBound classes) classes with
  | timeout | contradiction =>
      simp only [actual, SymbolicEqualityBridge.resultClasses, reduceCtorEq] at done
  | normalized result =>
      have same : result = output := by
        simpa only [actual, SymbolicEqualityBridge.resultClasses, Option.some.injEq] using done
      subst result
      exact mkEqConstraints_mem_original _ classes output prefixFree actual path member

/-- Actual source normalization preserves global prefix freedom across all returned classes. -/
theorem normalize_prefix_free (classes output : Constraints)
    (prefixFree : ∀ first ∈ members classes, ∀ second ∈ members classes,
      first.IsPrefix second → first = second)
    (done : SourceCompactGuards.normalize classes = some output)
    (first : Path) (firstMember : first ∈ members output)
    (second : Path) (secondMember : second ∈ members output)
    (initial : first.IsPrefix second) : first = second :=
  prefixFree first (normalize_mem_original classes output prefixFree done first firstMember)
    second (normalize_mem_original classes output prefixFree done second secondMember) initial

end MicroCFTA.EqualityNormalizePrefixFree
