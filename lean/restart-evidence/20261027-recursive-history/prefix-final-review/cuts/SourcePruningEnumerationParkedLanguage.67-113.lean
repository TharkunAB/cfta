/-- An actual repeated check drops exactly the selected bucket's suspended restrictions. -/
theorem checkRepeated_true_satisfies
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel uv handle : Nat) (scs : List Suspended)
    (before after : State Symbol EnumGuard)
    (ready : EnumerationDriver.Ready uv before)
    (stored : before.values[uv]? = some (.unenumerated (some handle) scs))
    (observed : Success (checkRepeated heap fuel uv handle scs) before true after) :
    Satisfies language meaning assignment before ↔
      Satisfies language meaning assignment after ∧
        ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc := by
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) before true after := by
        simpa only [checkRepeated, decoded] using observed
      exact (success_failure .unresolvedReference before after true impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [checkRepeated, decoded, boundary, ↓reduceIte] at observed
        obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp observed
        obtain ⟨same, _safe, _counter, _protected⟩ := EnumerationDriver.representative_root fuel uv root
          before resolved ready.safe ready.inside ready.root resolution
        subst root
        have frame := representative_frame fuel uv uv before resolved ready.safe.1.total resolution
        obtain ⟨current, currentState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨currentSame, stateSame⟩ := (EnumerationDriver.get_success resolved currentState current).mp reading
        subst current currentState
        by_cases seen : recursionKey handle scs ∈ resolved.recursionAncestry uv
        · simp only [seen, ↓reduceIte] at continued
          obtain ⟨token, cleared, written, returned⟩ := (success_bind _ _ _ _ _).mp continued
          cases token
          obtain ⟨_same, afterSame⟩ := (success_pure true true cleared after).mp returned
          subst after
          have resolvedStored : resolved.values[uv]? = some (.unenumerated (some handle) scs) := by
            simpa only [frame.values] using stored
          exact (SourcePruningEnumerationNativeLanguage.satisfies_frame language meaning assignment
            before resolved frame).symm.trans
            (clear_satisfies language meaning assignment resolved cleared uv (some handle) scs resolvedStored written)
        · have impossible : Success (pure false) resolved true after := by
            simpa only [seen, ↓reduceIte] using continued
          obtain ⟨impossible, _same⟩ := (success_pure false true resolved after).mp impossible
          cases impossible
      · have impossible : Success (pure false) before true after := by
          simpa only [checkRepeated, decoded, boundary, Bool.false_eq_true, ↓reduceIte] using observed
        obtain ⟨impossible, _same⟩ := (success_pure false true before after).mp impossible
        cases impossible
