theorem checkRepeated_created_isolated
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv handle : Nat) (scs : List Suspended)
    (before after : EnumerationState.State Symbol EnumGuard)
    (ready : EnumerationDriver.Ready uv before)
    (incoming : EnumerationReferences.IncomingAvoid uv before)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before true after) : IsolatedPending uv handle after := by
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) before true after := by
        simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded] using observed
      exact (success_failure .unresolvedReference before after true impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at observed
        obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp observed
        obtain ⟨same, resolvedSafe, counter, protectedRoot⟩ := EnumerationDriver.representative_root fuel uv root
          before resolved ready.safe ready.inside ready.root resolution
        subst root
        have frame := representative_frame fuel uv uv before resolved ready.safe.1.total resolution
        have resolvedIncoming := EnumerationPendingReplacement.frame_incoming uv before resolved frame incoming
        obtain ⟨current, currentState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨currentSame, stateSame⟩ := (EnumerationDriver.get_success resolved currentState current).mp reading
        subst current currentState
        by_cases seen : recursionKey handle scs ∈ resolved.recursionAncestry uv
        · simp only [seen, ↓reduceIte] at continued
          obtain ⟨token, cleared, written, returned⟩ := (success_bind _ _ _ _ _).mp continued
          cases token
          obtain ⟨_same, afterSame⟩ := (success_pure true true cleared after).mp returned
          subst after
          have shape := (EnumerationDriver.modify_success _ resolved cleared).mp written
          have inside : uv < resolved.values.length := by
            rw [← resolvedSafe.1.aligned, counter]
            exact ready.inside
          refine ⟨?_, ?_, EnumerationPendingReplacement.setValue_clear_incoming uv uv (some handle)
            resolved cleared resolvedIncoming written⟩
          · simpa only [shape] using protectedRoot.root
          · simpa only [shape] using
              (List.getElem?_set_self inside :
                (resolved.values.set uv (.unenumerated (some handle) []))[uv]? =
                  some (.unenumerated (some handle) []))
        · have impossible : Success (pure false) resolved true after := by
            simpa only [seen, ↓reduceIte] using continued
          obtain ⟨impossible, _same⟩ := (success_pure false true resolved after).mp impossible
          cases impossible
      · have impossible : Success (pure false) before true after := by
          simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary,
