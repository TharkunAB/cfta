theorem cache_of_related (caller : Caller width) {flat : FlatCached} {earlier : Cached}
    (related : EnumerationFlatCached.Related flat earlier) (valid : CacheValid caller earlier) :
    EnumerationFlatNativeIndex.Correct caller.checked.native.machine.heap flat := by
  obtain ⟨roots, paths, storage, _realized, counts, flags⟩ := valid
  exact EnumerationFlatNativeIndex.correct_of_related related caller.checked.native.machine.heap
    roots paths storage.aligned flags counts
