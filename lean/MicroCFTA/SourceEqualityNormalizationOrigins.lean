import MicroCFTA.SourceEqualityGuardReadback

/-!
# Symbolic path origins in completed normalization

The statements do not evaluate a concrete normalizer run.
-/
namespace MicroCFTA.SourceEqualityNormalizationOrigins
open EqualityNormalize SourceCompactGuards

/-- Every actual completed source normalization returns a congruence fixed point. -/
theorem normalize_fixed {input output : Constraints}
    (observed : normalize input = some output) : congruenceStep output = some output := by
  unfold normalize at observed
  rw [arrayNormalize_eq] at observed
  cases done : mkEqConstraints (EqualityTermination.normalizationBound input) input with
  | timeout | contradiction =>
      simp [done, SymbolicEqualityBridge.resultClasses] at observed
  | normalized result =>
      have same : result = output := by
        simpa [done, SymbolicEqualityBridge.resultClasses] using observed
      subst result
      exact (mkEqConstraints_invariants _ _ _ done).2.2.2

/-- A fixed point contains every actual extension induced by a recorded prefix. -/
theorem fixed_extension_mem {classes : Constraints}
    (fixed : congruenceStep classes = some classes)
    {paths : Class} (present : paths ∈ classes)
    {base replacement suffix : EqualityNormalize.Path}
    (baseMember : base ∈ paths) (replacementMember : replacement ∈ paths)
    (extension : base ++ suffix ∈ members classes) (nonempty : suffix ≠ []) :
    replacement ++ suffix ∈ members classes := by
  have suffixMember : suffix ∈ suffixes paths classes :=
    (mem_suffixes suffix paths classes).mpr
      ⟨base, baseMember, base ++ suffix, extension, nonempty, rfl⟩
  have generated : extendClass paths suffix ∈ addCongruences classes := by
    rw [addCongruences]
    exact List.mem_append.mpr (.inr (List.mem_flatMap.mpr
      ⟨paths, present, List.mem_map.mpr ⟨suffix, suffixMember, rfl⟩⟩))
  have generatedPath : replacement ++ suffix ∈ members (addCongruences classes) :=
    (mem_members _ _).mpr
      ⟨extendClass paths suffix, generated,
        (mem_extendClass _ _ _).mpr ⟨replacement, replacementMember, rfl⟩⟩
  have retained := (complete_members (addCongruences classes) (replacement ++ suffix)).mpr
    generatedPath
  have same : complete (addCongruences classes) = classes := by
    unfold congruenceStep at fixed
    dsimp only at fixed
    split at fixed
    · cases fixed
    · exact Option.some.inj fixed
  exact same ▸ retained


end MicroCFTA.SourceEqualityNormalizationOrigins
