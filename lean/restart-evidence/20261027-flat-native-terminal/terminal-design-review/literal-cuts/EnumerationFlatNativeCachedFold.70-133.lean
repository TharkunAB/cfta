    (beforeCaller : Caller width) (target : Nat) (queries : Queries) :
    ResultRelated (run checkEmpty nativeFuel p h sources beforeCaller flat target queries)
      (SourcePruningEnumerationCachedFold.run checkEmpty nativeFuel p h sources
        beforeCaller earlier target queries) := by
  induction sources generalizing flat earlier beforeCaller queries with
  | nil => exact ⟨⟨rfl, rfl, related.core, .cons (.ok () related.core) .nil⟩, related⟩
  | cons source rest ih =>
    have step := EnumerationFlatNativeCachedAdapter.run_related related checkEmpty nativeFuel p h
      beforeCaller source target queries
    generalize leftRun : EnumerationFlatNativeCachedAdapter.run checkEmpty nativeFuel p h
      beforeCaller flat source target queries = left at step ⊢
    generalize rightRun : SourcePruningEnumerationCachedAdapter.run checkEmpty nativeFuel p h
      beforeCaller earlier source target queries = right at step ⊢
    obtain ⟨leftOutcome, reachedCaller, savedQueries, leftCache⟩ := left
    obtain ⟨rightOutcome, oldCaller, oldQueries, rightCache⟩ := right
    obtain ⟨callerSame, queriesSame, caches, rows⟩ := step
    dsimp only at callerSame queriesSame
    subst oldCaller
    subst oldQueries
    dsimp only at rows caches
    simp only [run, SourcePruningEnumerationCachedFold.run, leftRun, rightRun]
    cases leftOutcome with
    | error first =>
      cases rightOutcome with
      | error second => exact ⟨⟨rfl, rfl, related.core, rows⟩, trivial⟩
      | ok returned => cases rows
    | ok leftReturned =>
      cases rightOutcome with
      | error fault => cases leftReturned <;> cases rows
      | ok rightReturned =>
        cases leftReturned with
        | none =>
          cases rightReturned with
          | none => exact ⟨⟨rfl, rfl, related.core, trivial⟩, trivial⟩
          | some raw => cases rows
        | some flatRows =>
          cases rightReturned with
          | none => cases rows
          | some oldRows =>
            dsimp only
            cases rows with
            | nil => exact ⟨⟨rfl, rfl, related.core, .nil⟩, caches⟩
            | cons head tail =>
              cases head with
              | error fault => exact ⟨⟨rfl, rfl, related.core, .cons (.error fault) tail⟩, caches⟩
              | ok value states =>
                cases value
                cases tail with
                | cons next remaining =>
                    exact ⟨⟨rfl, rfl, related.core, .cons (.ok () states) (.cons next remaining)⟩, caches⟩
                | nil =>
                  cases leftCache with
                  | none =>
                    cases rightCache with
                    | none => exact ⟨EnumerationFlatNativeFold.run_related states checkEmpty nativeFuel p h
                        rest reachedCaller target savedQueries, trivial⟩
                    | some oldCache => cases caches
                  | some flatCache =>
                    cases rightCache with
                    | none => cases caches
                    | some oldCache =>
                      exact ih (frame_related caches states) reachedCaller savedQueries

end MicroCFTA.EnumerationFlatNativeCachedFold
