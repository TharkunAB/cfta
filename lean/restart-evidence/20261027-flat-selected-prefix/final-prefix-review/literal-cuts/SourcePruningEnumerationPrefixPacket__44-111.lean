/-- Every narrowed prefix retains its actual native Post, including Empty rejection. -/
theorem prefix_context (observed : Result width Typing)
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos observed) :
    match observed with
    | .stopped _ _ => False
    | .parked _ _ _ => True
    | .narrowed _ _ reached queries _ _ _ _ =>
        ∃ final, Post formulas solver inventory caller reached final ∧ final.query = queries := by
  have full := valid.2.1
  cases observed with
  | stopped read checked =>
      obtain ⟨_oldHandle, _scs, _readAfter, _reading, impossible⟩ := full
      exact impossible
  | parked _ _ _ => trivial
  | narrowed checked prepared reached queries action candidate right ordinary =>
      obtain ⟨next, finished⟩ := finish_preserves checkEmpty edgesOf 0 0 0 0 0 uv
        (.narrowed checked prepared reached queries action candidate right ordinary)
      rw [finished] at full
      obtain ⟨_oldHandle, _scs, _readAfter, _reading, _checking, _oldValue, _value, _heap,
        _selectedAction, final, _decoded, _narrowed, _prepared, _samePrepared, _reached,
        _queries, post, saved, _shape⟩ := full
      exact ⟨final, post, saved⟩

/-- Every retained parked or nonempty cache has its actual native laws and original counter and order. -/
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
  have full := valid.2.1
  cases observed with
  | stopped _ _ => trivial
  | parked checked candidate raw =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨_oldHandle, _scs, _readAfter, _reading, _checking, cached, same, _core,
            cacheValid, safe, pending, _counter, _ordered, _raw⟩ := full
          have equal : after = cached := Option.some.inj same
          subst cached
          exact ⟨cacheValid, safe, pending, valid.2.2⟩
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨next, finished⟩ := finish_preserves checkEmpty edgesOf 0 0 0 0 0 uv
            (.narrowed checked prepared reached queries action (some after) right ordinary)
          rw [finished] at full
          obtain ⟨_oldHandle, _scs, _readAfter, _reading, _checking, _oldValue, _value, _heap,
            _selectedAction, _final, _decoded, _narrowed, _prepared, _samePrepared, _reached,
            _queries, _post, _saved, shape⟩ := full
          rcases shape with ⟨_empty, _action, noCache, _right, _ordinary⟩ |
            ⟨_newHandle, cached, _nonempty, _encoded, _action, same, cacheValid, safe, pending, _rest⟩
          · cases noCache
          · have equal : after = cached := Option.some.inj same
            subst cached
            exact ⟨cacheValid, safe, pending, valid.2.2⟩
