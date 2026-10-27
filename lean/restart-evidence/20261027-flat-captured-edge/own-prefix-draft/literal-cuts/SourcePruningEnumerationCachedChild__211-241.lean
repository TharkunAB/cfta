  have nativeRun : ∀ (extra : Nat), writeSlot heap (fuel + extra) before.core.counter
      (.unenumerated (some handle) scs) allocatedCached = some saved := by
    intro extra
    simp only [writeSlot, allocatedStored, Option.bind_some, references,
      SourcePruningEnumerationNativeIndex.write, SourcePruningEnumerationNativeIndex.candidate,
      decoded, Option.map_some, MergedOrdinaryHeight.recursiveBoundary,
      Bool.false_and, Bool.not_false,
      show SourcePruningEnumerationNativeIndex.count (fuel + extra)
        allocatedCached.core.representatives (-1) [] allocatedCached.waiting =
        some allocatedCached.waiting from rfl,
      countRun extra 1 allocatedCached.waiting, saved]
  have coreRaw : ExceptT.run (action before.core) =
      [.ok (.hole before.core.counter, saved.core)] := by
    simp only [SourcePruningEnumerationShallowChild.prepareChild, nonterminal,
      Bool.false_eq_true, ↓reduceIte, encoded, Option.some.injEq] at prepared
    rw [← prepared]
    change [(.ok (.hole before.core.counter,
      {EnumerationState.allocated (some handle) before.core with
        values := (EnumerationState.allocated (some handle) before.core).values.set
          before.core.counter (.unenumerated (some handle) scs)}) :
            Except EnumerationState.Error
              (Fragments.Fragment Symbol × EnumerationState.State Symbol EnumGuard))] = _
    rw [savedCore, afterShape]
  refine ⟨handle, action, allocatedCached, saved, fuel, encoded, decoded, prepared, coreRaw,
    nativeAllocated, allocatedShape, allocatedStored, allocatedStorage, allocatedRealized,
    allocatedCounts, allocatedFlags, waitingSame, nativeRun, ?_, rfl, ?_, ?_, ?_, ?_, ?_,
    savedStorage, ?_, savedCounts, savedFlags, ?_, ?_, ?_⟩
  · intro extra
    simp only [prepareOrdinary, nonterminal, Bool.false_eq_true, ↓reduceIte, encoded,
      Option.bind_some, nativeAllocated, nativeRun extra, Option.map_some]
  · simpa only [savedCore] using afterSlot
