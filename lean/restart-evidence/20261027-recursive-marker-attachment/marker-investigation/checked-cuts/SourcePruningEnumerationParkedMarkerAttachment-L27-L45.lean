private theorem repeated_native_boundary
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel uv handle : Nat)
    (scs : List Suspended) (before after : Core)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before true after) :
    ∃ value, lookupNode heap handle = some value ∧ MergedOrdinaryHeight.recursiveBoundary value = true := by
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) before true after := by
        simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded] using observed
      exact (success_failure .unresolvedReference before after true impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · exact ⟨value, rfl, boundary⟩
      · have impossible : Success (pure false) before true after := by
          simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary,
            Bool.false_eq_true, ↓reduceIte] using observed
        obtain ⟨impossible, _same⟩ := (success_pure false true before after).mp impossible
        cases impossible
