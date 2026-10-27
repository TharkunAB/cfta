    simpa only [congrArg EnumerationState.State.values joinedSame] using flags
  let joinedCache : EnumerationExpandableIndex.Cached Symbol Constraint :=
    ⟨joined, before.expandable, moved⟩
  obtain ⟨foldFuel, foldP, foldH, foldRows, foldCaller, foldQueries, foldFinal, foldInventory,
    folded, cachedFoldRun, foldPost, foldQuerySame, foldCounter, foldForest, foldPaths,
    foldStorage, foldRealized, foldCounts, foldWaiting, foldFlags, foldShape, foldPending,
    foldEliminated, foldCompleted, foldFrame, foldOrigin⟩ :=
    SourcePruningEnumerationCachedFoldCompletion.complete formulas solver inventory beforeCaller
      joinedCache recorded checkEmpty winner memos
      (EnumerationCanonicalUnion.mergedRoots roots recorded winner) initial joinedStorage
      joinedRealized prefixRoots prefixCounts joinedFlags winnerPending
      (fun source member => .inl (recordedPending source member))
      (ranges prefixFuel recorded winner moved joined (by simpa only [Nat.add_zero] using prefixRun 0)).1
  have foldRun : ∀ extra P H, foldP ≤ P → foldH ≤ H →
      SourcePruningEnumerationFold.run checkEmpty (foldFuel + extra) P H recorded
        beforeCaller joined winner memos.query =
        (.ok (some (foldRows.map (fun row => .ok (row.1, row.2.core)))),
          foldCaller, foldQueries, folded.core) := by
    intro extra P H enoughP enoughH
    rw [← SourcePruningEnumerationCachedFold.erase checkEmpty (foldFuel + extra) P H
      recorded beforeCaller joinedCache winner memos.query]
    exact congrArg Prod.fst (cachedFoldRun extra P H enoughP enoughH)
  have foldedRoot : IsRoot folded.core.representatives winner := by
    simpa only [foldForest] using joinedRoot
  have foldedFrame : ∀ (slot : Nat), slot ∉ recorded →
      folded.core.values[slot]? = before.core.values[slot]? := by
    intro slot outside
    have different : slot ≠ winner := fun same => outside (same ▸ winnerMember)
    rw [foldFrame slot outside different]
    exact congrArg (fun state => state.values[slot]?) joinedSame
  have foldedSafe : foldRows = [((), folded)] → Safe folded.core := by
    intro completed
    refine ⟨foldStorage, ?_⟩
    intro slot value stored
    by_cases atWinner : slot = winner
    · subst slot
      obtain ⟨node, scs, pendingRead⟩ := foldPending
      have valueSame : value = .unenumerated node scs := Option.some.inj (stored.symm.trans pendingRead)
      exact ⟨fun _ => foldedRoot, fun _ => by simp only [valueSame, ne_eq, reduceCtorEq, not_false_eq_true]⟩
    · by_cases selected : slot ∈ recorded
      · have eliminated : value = .eliminated :=
          Option.some.inj (stored.symm.trans (foldCompleted completed slot selected atWinner))
        have fixed : roots slot = slot := by
          rw [recordedSame] at selected
          obtain ⟨sc, _member, named⟩ := List.mem_map.mp selected
          simpa only [named] using EnumerationCanonicalUnion.roots_idempotent
            before.core.representatives roots paths sc.var
        have notRoot : ¬ IsRoot folded.core.representatives slot := by
          intro root
          have named := (root_iff _ _ foldPaths slot).mp root
          simp only [EnumerationCanonicalUnion.mergedRoots, fixed, ite_eq_left selected] at named
          exact atWinner named.symm
        exact ⟨fun live => (live eliminated).elim, fun root => (notRoot root).elim⟩
      · have originalStored : before.core.values[slot]? = some value := by
          rw [← foldedFrame slot selected]
