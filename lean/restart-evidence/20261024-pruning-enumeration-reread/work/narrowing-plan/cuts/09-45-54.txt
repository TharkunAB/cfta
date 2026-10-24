theorem realized_preserved (heap nextHeap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : EnumerationState.State Symbol EnumGuard)
    (realized : PendingRealized heap before) (frame : Frame before after)
    (kept : SourceEqualityRequiredCache.Keeps heap nextHeap) : PendingRealized nextHeap after := by
  intro slot node scs stored
  have earlierStored : before.values[slot]? = some (.unenumerated (some node) scs) := by
    simpa only [frame.values] using stored
  obtain ⟨value, decoded, available, closed⟩ := realized slot node scs earlierStored
  exact ⟨value, lookupNode_keeps heap nextHeap kept node value decoded,
    available.grows heap nextHeap kept.growth kept.history, closed⟩
