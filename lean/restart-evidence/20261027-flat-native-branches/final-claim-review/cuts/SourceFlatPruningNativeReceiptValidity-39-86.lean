theorem of_related (target : Nat) (flat : FlatReceipt width) (earlier : Receipt width)
    (admitted : Admitted target earlier)
    (related : SourceFlatPruningSelectedEdge.ResultRelated flat earlier) : Indexed flat := by
  cases flat with
  | unhandled => trivial
  | rejected reached saved recovered =>
      change EnumerationFlatNativeIndex.Correct reached.checked.native.machine.heap recovered
      cases earlier with
      | unhandled | complete _ _ _ _ | stopped _ _ _ => cases related
      | rejected oldCaller oldQueries oldAfter =>
          obtain ⟨callerSame, _queriesSame, caches⟩ := related
          rw [callerSame]
          exact cache_of_related oldCaller caches admitted
  | complete fragment reached saved recovered =>
      change EnumerationFlatNativeIndex.Correct reached.checked.native.machine.heap recovered
      cases earlier with
      | unhandled | rejected _ _ _ | stopped _ _ _ => cases related
      | complete oldFragment oldCaller oldQueries oldAfter =>
          obtain ⟨_fragmentSame, callerSame, _queriesSame, caches⟩ := related
          rw [callerSame]
          exact cache_of_related oldCaller caches admitted.1
  | stopped fragments observation candidate =>
      cases candidate with
      | none => trivial
      | some recovered =>
          change EnumerationFlatNativeIndex.Correct observation.2.1.checked.native.machine.heap recovered
          cases earlier with
          | unhandled | rejected _ _ _ | complete _ _ _ _ => cases related
          | stopped oldFragments oldObservation oldCandidate =>
              obtain ⟨oldOutcome, oldCaller, oldQueries, oldOuter, oldWaiting⟩ := oldObservation
              obtain ⟨_fragmentsSame,
                ⟨callerSame, _queriesSame, _outerRelated, _waitingSame, _rowsRelated⟩,
                caches⟩ := related
              cases oldCandidate with
              | none => cases caches
              | some oldAfter =>
                  cases oldOutcome with
                  | error fault => cases admitted
                  | ok returned =>
                      cases returned with
                      | none => cases admitted
                      | some rows =>
                          cases rows with
                          | cons row rest => cases admitted
                          | nil =>
                              dsimp only at callerSame
                              rw [callerSame]
                              exact cache_of_related oldCaller caches admitted
