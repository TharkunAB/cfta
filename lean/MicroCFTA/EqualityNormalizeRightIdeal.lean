import MicroCFTA.SourceCompactGuards

/-!
# Path predicates through actual equality normalization

Preparation removes endpoints. Completion preserves endpoint membership.
Congruence generation appends a suffix to an existing endpoint. A predicate
closed under right extension therefore holds after successful normalization.
-/
namespace MicroCFTA.EqualityNormalizeRightIdeal
open EqualityNormalize

private theorem prepare_preserves (P : Path → Prop) (classes : Constraints)
    (inputs : ∀ path ∈ members classes, P path) :
    ∀ path ∈ members (prepare classes), P path := by
  intro path member
  obtain ⟨paths, present, atPath⟩ := (mem_members _ _).mp member
  obtain ⟨mapped, _⟩ := List.mem_filter.mp present
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp mapped
  exact inputs path ((mem_members _ _).mpr ⟨original, originalMember, by simpa using atPath⟩)

private theorem addCongruences_preserves (P : Path → Prop)
    (rightClosed : ∀ path, P path → ∀ suffix, P (path ++ suffix))
    (classes : Constraints) (inputs : ∀ path ∈ members classes, P path) :
    ∀ path ∈ members (addCongruences classes), P path := by
  intro path member
  obtain ⟨paths, present, atPath⟩ := (mem_members _ _).mp member
  rcases List.mem_append.mp present with original | generated
  · exact inputs path ((mem_members _ _).mpr ⟨paths, original, atPath⟩)
  · obtain ⟨source, sourceMember, built⟩ := List.mem_flatMap.mp generated
    obtain ⟨suffix, _, rfl⟩ := List.mem_map.mp built
    obtain ⟨base, baseMember, rfl⟩ := (mem_extendClass _ _ _).mp atPath
    exact rightClosed base (inputs base ((mem_members _ _).mpr ⟨source, sourceMember, baseMember⟩)) suffix

private theorem step_preserves (P : Path → Prop)
    (rightClosed : ∀ path, P path → ∀ suffix, P (path ++ suffix))
    (classes output : Constraints) (inputs : ∀ path ∈ members classes, P path)
    (done : congruenceStep classes = some output) :
    ∀ path ∈ members output, P path := by
  have closed : complete (addCongruences classes) = output := by
    dsimp only [congruenceStep] at done
    split at done
    · cases done
    · exact Option.some.inj done
  intro path member
  rw [← closed] at member
  exact addCongruences_preserves P rightClosed classes inputs path
    ((complete_members (addCongruences classes) path).mp member)

private theorem fixMaybe_preserves (P : Path → Prop)
    (rightClosed : ∀ path, P path → ∀ suffix, P (path ++ suffix))
    (fuel : Nat) (classes output : Constraints) (inputs : ∀ path ∈ members classes, P path)
    (done : fixMaybe fuel classes = .normalized output) :
    ∀ path ∈ members output, P path := by
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
            exact inputs
          · have recursive : fixMaybe fuel next = .normalized output := by
              simpa only [fixMaybe, stepped, stable, ↓reduceIte] using done
            exact ih next (step_preserves P rightClosed classes next inputs stepped) recursive

/-- Successful bounded normalization preserves predicates closed under right extension. -/
theorem mkEqConstraints_preserves (P : Path → Prop)
    (rightClosed : ∀ path, P path → ∀ suffix, P (path ++ suffix))
    (fuel : Nat) (classes output : Constraints) (inputs : ∀ path ∈ members classes, P path)
    (done : mkEqConstraints fuel classes = .normalized output) :
    ∀ path ∈ members output, P path := by
  apply fixMaybe_preserves P rightClosed fuel (complete (prepare classes)) output ?_ done
  intro path member
  exact prepare_preserves P classes inputs path ((complete_members (prepare classes) path).mp member)

/-- Successful actual source normalization preserves the same path predicates. -/
theorem normalize_preserves (P : Path → Prop)
    (rightClosed : ∀ path, P path → ∀ suffix, P (path ++ suffix))
    (classes output : Constraints) (inputs : ∀ path ∈ members classes, P path)
    (done : SourceCompactGuards.normalize classes = some output) :
    ∀ path ∈ members output, P path := by
  unfold SourceCompactGuards.normalize at done
  rw [SourceCompactGuards.arrayNormalize_eq] at done
  cases actual : mkEqConstraints (EqualityTermination.normalizationBound classes) classes with
  | timeout | contradiction =>
      simp only [actual, SymbolicEqualityBridge.resultClasses, reduceCtorEq] at done
  | normalized result =>
      have same : result = output := by
        simpa only [actual, SymbolicEqualityBridge.resultClasses, Option.some.injEq] using done
      subst result
      exact mkEqConstraints_preserves P rightClosed _ classes output inputs actual

end MicroCFTA.EqualityNormalizeRightIdeal
