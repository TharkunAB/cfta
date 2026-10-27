theorem prefix_cache_valid (observed : Result width Typing)
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos observed) :
    match observed with
    | .parked _ (some after) _ =>
        SourcePruningEnumerationNativeBranchCompletion.CacheValid caller after ∧ Safe after.core ∧
        EnumerationReferences.PendingReferences after.core ∧ after.core.counter = before.core.counter ∧
        ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
          EnumerationOrder.Stratified after.core level frontier
    | .narrowed _ _ reached _ _ (some after) _ _ =>
        SourcePruningEnumerationNativeBranchCompletion.CacheValid reached after ∧ Safe after.core ∧
        EnumerationReferences.PendingReferences after.core ∧ after.core.counter = before.core.counter ∧
        ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
          EnumerationOrder.Stratified after.core level frontier
    | _ => True := by
