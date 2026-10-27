theorem candidates_nil_iff_native_frontier
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : Cached) (earlier : EnumerationExpandableIndex.Cached Symbol Constraint)
    (related : EnumerationFlatCached.Related before earlier)
    (correct : EnumerationFlatNativeIndex.Correct heap before)
    (realized : SourcePruningEnumerationObservation.PendingRealized heap earlier.core) :
    candidates before = [] ↔
      ∀ (uv handle : Nat) (scs : List Suspended), before.core.values[uv]? = some (.unenumerated (some handle) scs) →
        ∃ value, lookupNode heap handle = some value ∧
          InternedProbeProvenance.Available heap value ∧ value.free = [] ∧
          MergedOrdinaryHeight.recursiveBoundary value = true ∧ scs = [] := by
