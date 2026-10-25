theorem allocate_node_flags
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard) (handle : Nat)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (InternedConstructorTemplates.EdgeValue Symbol NativeGuard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (decoded : lookupNode heap handle = some (.node entry edges depth free))
    (aligned : before.core.counter = before.core.values.length)
    (flags : ∀ (slot : Nat),
      SourcePruningEnumerationNativeIndex.candidate heap
        ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ allocatedCached : EnumerationExpandableIndex.Cached Symbol EnumGuard,
      allocate heap (some handle) before = some (before.core.counter, allocatedCached) ∧
      allocatedCached.core = EnumerationState.allocated (some handle) before.core ∧
      allocatedCached.waiting = before.waiting ∧
      allocatedCached.expandable =
        (fun slot => if slot = before.core.counter then true else before.expandable slot) ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
        ((allocatedCached.core.values[slot]?).getD .eliminated) =
          some (allocatedCached.expandable slot)) := by
  have candidateTrue : SourcePruningEnumerationNativeIndex.candidate heap
      (.unenumerated (some handle) []) = some true := by
    simp only [SourcePruningEnumerationNativeIndex.candidate, decoded, Option.map_some,
      MergedOrdinaryHeight.recursiveBoundary, Bool.false_and, Bool.not_false]
  refine ⟨⟨EnumerationState.allocated (some handle) before.core,
    fun slot => if slot = before.core.counter then true else before.expandable slot,
    before.waiting⟩, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [allocate, candidateTrue, Option.map_some, ↓reduceIte]
  · intro slot
    by_cases beforeSlot : slot < before.core.values.length
    · have different : slot ≠ before.core.counter := by
        rw [aligned]
        omega
      simpa only [EnumerationState.allocated, List.getElem?_append_left beforeSlot,
        ite_eq_right different] using flags slot
    · by_cases same : slot = before.core.counter
      · subst slot
        simpa only [EnumerationState.allocated_slot (some handle) before.core aligned,
          Option.getD_some, ↓reduceIte] using candidateTrue
      · have absent : before.core.values[slot]? = none := by
          exact List.getElem?_eq_none (by omega)
        have wholeAbsent : (EnumerationState.allocated (some handle) before.core).values[slot]? = none := by
          apply List.getElem?_eq_none
          simp only [EnumerationState.allocated, List.length_append, List.length_singleton]
          omega
        simpa only [wholeAbsent, absent, Option.getD_none, ite_eq_right same] using flags slot

