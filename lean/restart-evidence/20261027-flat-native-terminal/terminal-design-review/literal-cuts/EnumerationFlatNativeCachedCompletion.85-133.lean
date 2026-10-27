  let roots := FlatUnionFind.root flat.core.representatives
  have paths : Roots before.core.representatives roots :=
    EnumerationFlatNativeIndex.related_roots related.core.representatives
  have counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting := by
    rw [← related.core.values, ← related.waiting]
    exact correct.waiting
  have flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate
      beforeCaller.checked.native.machine.heap ((before.core.values[slot]?).getD .eliminated) =
        some (before.expandable slot) := by
    intro slot
    rw [← related.core.values, ← related.expandable]
    exact correct.expandable slot
  obtain ⟨fuel, p, h, rows, afterCaller, savedQueries, final, next, after,
    stable, post, querySame, counterSame, representativesSame, afterPaths, afterStorage,
    afterRealized, afterCounts, waitingSame, afterFlags, shape, afterTarget, eliminated,
    completed, frame, origin⟩ :=
      SourcePruningEnumerationCachedFoldCompletion.complete formulas solver inventory beforeCaller
        before sources checkEmpty target memos roots initial storage realized paths counts flags
        targetPending selected ranges
  refine ⟨fuel, p, h, rows, afterCaller, savedQueries, final, next, after,
    stable, post, querySame, counterSame, representativesSame, afterPaths, afterStorage,
    afterRealized, afterCounts, waitingSame, afterFlags, shape, afterTarget, eliminated,
    completed, frame, origin, ?_⟩
  intro extra P H pBound hBound
  have correspondence := EnumerationFlatNativeCachedFold.run_related related checkEmpty
    (fuel + extra) P H sources beforeCaller target memos.query
  rw [stable extra P H pBound hBound] at correspondence
  generalize actual : EnumerationFlatNativeCachedFold.run checkEmpty (fuel + extra) P H
    sources beforeCaller flat target memos.query = observed at correspondence
  obtain ⟨⟨outcome, reachedCaller, returnedQueries, outer⟩, recovered⟩ := observed
  obtain ⟨⟨callerSame, queriesSame, outerRelated, rowRelated⟩, cacheRelated⟩ := correspondence
  dsimp only at callerSame queriesSame outerRelated rowRelated cacheRelated
  subst reachedCaller
  subst returnedQueries
  cases recovered with
  | none => cases cacheRelated
  | some recovered =>
    cases outcome with
    | error fault => cases rowRelated
    | ok returned =>
      cases returned with
      | none => cases rowRelated
      | some flatRows =>
        exact ⟨flatRows, outer, recovered, rfl, cacheRelated, outerRelated, rowRelated,
          EnumerationFlatNativeIndex.correct_of_related cacheRelated
            afterCaller.checked.native.machine.heap roots afterPaths afterStorage.aligned
            afterFlags afterCounts⟩

end MicroCFTA.EnumerationFlatNativeCachedCompletion
