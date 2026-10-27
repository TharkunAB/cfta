    (aligned : earlier.core.counter = earlier.core.values.length)
    (flags : ∀ uv, SourcePruningEnumerationNativeIndex.candidate heap
      ((earlier.core.values[uv]?).getD .eliminated) = some (earlier.expandable uv))
    (waiting : EnumerationCanonicalWaiting.Correct roots earlier.core.values earlier.waiting) :
    Correct heap flat := by
  have sameRoots : FlatUnionFind.root flat.core.representatives = roots := by
    funext uv
    obtain ⟨size, path⟩ := paths uv
    exact (UnionFind.reaches_unique (related.core.representatives uv) path).1
  refine ⟨?_, ?_, ?_⟩
  · rw [related.core.counter, related.core.values]
    exact aligned
  · intro uv
    rw [related.core.values, related.expandable]
    exact flags uv
  · rw [sameRoots, related.core.values, related.waiting]
    exact waiting

/-- Replacing all old references by all new references derives both native indexes. -/
theorem write_correct (heap : InternedConstructorTemplates.State Symbol NativeGuard)
