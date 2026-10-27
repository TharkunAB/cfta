def cached (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (before : EnumerationFlatCached.Cached Symbol EnumGuard) :
    List (Except EnumerationState.Error
      ((List Nat × Nat) × EnumerationFlatCached.Cached Symbol EnumGuard)) :=
  (ExceptT.run (run first rest before.waiting before.core)).map fun row =>
    match row with
    | .error error => .error error
    | .ok ((recorded, winner, moved), after) =>
        .ok ((recorded, winner), ⟨after, before.expandable, moved⟩)

/-- The same actual cached prefix derives its final native indexes and earlier pending packet. -/
theorem cached_complete (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (flat : EnumerationFlatCached.Cached Symbol EnumGuard)
    (earlier : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (related : EnumerationFlatCached.Related flat earlier)
    (correct : EnumerationFlatNativeIndex.Correct heap flat)
    (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (safe : EnumerationSchedule.Safe earlier.core)
    (bounded : ∀ sc ∈ first :: rest, sc.var < flat.core.counter)
    (pending : EnumerationDependencies.InputsPending earlier.core (first :: rest))
    (realized : SourcePruningEnumerationObservation.PendingRealized heap earlier.core) :
    ∃ fuel recorded winner after oldAfter,
      cached first rest flat = [.ok ((recorded, winner), after)] ∧
      (∀ extra, ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        (fuel + extra) first rest earlier.waiting earlier.core) =
        [.ok ((recorded, winner, after.waiting), oldAfter.core)]) ∧
      EnumerationFlatCached.Related after oldAfter ∧ EnumerationFlatNativeIndex.Correct heap after ∧
      after.expandable = flat.expandable ∧ oldAfter.expandable = earlier.expandable ∧
      oldAfter.waiting = after.waiting ∧
      recorded = (first :: rest).map (fun sc => FlatUnionFind.root flat.core.representatives sc.var) ∧
      after.waiting = EnumerationCanonicalWaiting.moveMany winner
        (EnumerationBuilderCaches.canonicalIds (recorded.filter fun key => key != winner)) flat.waiting ∧
      winner ∈ recorded ∧
      EnumerationCorrectness.StorageValid oldAfter.core ∧
      SourcePruningEnumerationObservation.PendingRealized heap oldAfter.core ∧
      EnumerationCompleteness.PendingAt oldAfter.core winner ∧
      (∀ source, source ∈ recorded → EnumerationCompleteness.PendingAt oldAfter.core source) := by
  obtain ⟨fuel, recorded, winner, saved, _scanned, _united, oldAfter, after,
    flatRun, oldRun, finalRelated, _scan, _unions, _read, recordedSame, savedSame,
    winnerMember, _winnerFixed, _roots, counts, afterSame, storage, finalRealized,
    winnerPending, sourcesPending, _nodup, _ordered, _keys⟩ :=
    run_complete heap flat.core earlier.core related.core first rest flat.waiting
      correct.waiting safe bounded pending realized
  have values : after.values = flat.core.values := by
    rw [finalRelated.values, afterSame]
    exact related.core.values.symm
  have counter : after.counter = flat.core.counter := by
    rw [finalRelated.counter, afterSame]
    exact related.core.counter.symm
  let next : EnumerationFlatCached.Cached Symbol EnumGuard := ⟨after, flat.expandable, saved⟩
  let oldNext : EnumerationExpandableIndex.Cached Symbol EnumGuard :=
    ⟨oldAfter, earlier.expandable, saved⟩
  have nextCorrect : EnumerationFlatNativeIndex.Correct heap next := by
    refine ⟨?_, ?_, counts⟩
    · change after.counter = after.values.length
      rw [counter, values]
      exact correct.aligned
    · intro uv
      simpa only [next, values] using correct.expandable uv
  refine ⟨fuel, recorded, winner, next, oldNext, ?_, ?_,
    ⟨finalRelated, related.expandable, rfl⟩, nextCorrect, rfl, rfl, rfl,
    recordedSame, savedSame, winnerMember, storage, finalRealized, winnerPending, sourcesPending⟩
  · simp only [cached, ExceptT.run, flatRun, List.map_cons, List.map_nil]
    rfl
  · intro extra
    rw [← related.waiting]
    exact oldRun extra

end MicroCFTA.EnumerationFlatTerminalPrefix
