                  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient incoming term ∧
                  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient old term) ∧
              (checkEmpty = false → replacement = query ∧
                afterCaller = SourceCurrentAllocatedPartialState.advance foldCaller queried foldCaller.fourth foldCaller.merge ∧
                final = foldFinal))) := by
  obtain ⟨r, n, p, h, recorded, winner, joined, foldRows, foldCaller, foldQueries,
    foldFinal, foldInventory, folded, raw, afterCaller, outer, savedQueries, final, next,
    prefixRun, recordedSame, winnerMember, movedSame, joinedSame, joinedFlagsSame,
    prefixRoots, prefixCounts, joinedFlags, cachedFoldRun, foldRun, foldShape, foldPost,
    foldQuerySame, foldCounter, foldForest, foldPaths, foldStorage, foldRealized, foldedRoot,
    foldPending, foldCounts, foldWaiting, foldFlags, foldEliminated, foldCompleted,
    foldedFrame, foldedSafe, foldedOrigin,
    terminalRun, post, querySame, rejectedBranch, completedBranch⟩ :=
    SourcePruningEnumerationCachedTerminal.complete formulas solver inventory beforeCaller before
      checkEmpty first rest incoming incomingScs roots memos initial safe paths counts flags
      bounded pending realized nonempty available closed incomingBounded ranges
  have foldAllowed : ∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
      EnumerationReferences.ReferencesAllowed allowed folded.core := by
    intro allowed valid
    have values := congrArg EnumerationState.State.values joinedSame
    change joined.core.values = before.core.values at values
    apply SourcePruningEnumerationNativeReferences.fold_allowed allowed checkEmpty n p h recorded
      beforeCaller joined.core winner memos.query _ foldCaller foldQueries folded.core
      (by simpa only [EnumerationReferences.ReferencesAllowed, values] using valid)
    simpa only [Nat.add_zero] using foldRun 0 p h (Nat.le_refl _) (Nat.le_refl _)
  rcases foldShape with rejected | completed
  · subst foldRows
    obtain ⟨rawNil, callerSame, queriesSame, outerSame, _finalSame, _nextSame⟩ := rejectedBranch rfl
    refine ⟨r, n, p, h, 0, recorded, winner, joined, [], foldCaller, foldQueries, foldFinal,
      foldInventory, folded, raw, afterCaller, outer, savedQueries, final, next, folded,
      prefixRun, recordedSame, winnerMember, movedSame, joinedSame, joinedFlagsSame,
      prefixRoots, prefixCounts, joinedFlags, cachedFoldRun, foldRun, .inl rfl, foldPost,
      foldQuerySame, foldCounter, foldForest, foldPaths, foldStorage, foldRealized, foldedRoot,
      foldPending, foldCounts, foldWaiting, foldFlags, foldEliminated, foldCompleted,
      foldedFrame, foldedSafe, foldedOrigin,
      terminalRun, post, querySame, ?_,
      (by simpa only [congrArg EnumerationState.State.counter joinedSame] using foldCounter), foldPaths,
      foldStorage, ?_, foldCounts, ?_, foldedFrame, ?_,
      (protects before.core folded.core roots first rest recorded winner paths recordedSame
        winnerMember foldPaths foldedFrame), foldedOrigin, (fun allowed valid _ => foldAllowed allowed valid),
      ?_, rejectedBranch, ?_⟩
    · intro extraRepresentative extraNative P H extraIndex enoughP enoughH
      rw [rawNil, callerSame, queriesSame, outerSame]
      simp only [run, ite_eq_right nonempty, prefixRun extraRepresentative,
        ← joinedFlagsSame, cachedFoldRun extraNative P H enoughP enoughH, List.map_nil]
    · simpa only [callerSame] using foldRealized
    · simpa only [callerSame] using foldFlags
    · intro survives
      exact (survives rawNil).elim
    · intro isRejected
      rfl
    · intro isCompleted
      cases isCompleted
  · subst foldRows
    obtain ⟨incomingK, oldNode, oldScs, read, after, replacement, handle, outerRead, reading,
      frame, incomingRun, writePrefix, afterSame, afterStored, afterStorage, afterRealized,
      incomingPost, unfolding, cacheRun, afterCounter, afterRepresentatives, afterPaths,
      afterCounts, writeWaiting, afterFlags, afterExpandable, rawSame, winnerBound,
      replacementAvailable, replacementClosed, encoded, decoded, optional, present⟩ := completedBranch rfl
    obtain ⟨found, lookup, oldStored, _readSame⟩ :=
      (getValue_success r winner folded.core read (.unenumerated oldNode oldScs)).mp (by
        unfold Success
        rw [show ExceptT.run (getValue r winner folded.core) =
          [.ok (.unenumerated oldNode oldScs, read)] from
            by simpa only [Nat.add_zero] using reading 0]
        exact List.mem_singleton_self _)
    have foundTarget : found.representative = winner := by
      obtain ⟨rootSize, rootPath⟩ := foldedRoot
      exact (UnionFind.reaches_unique
        (UnionFind.findRoot_correct r folded.core.representatives winner found lookup).1 rootPath).1
    have readStored : read.values[winner]? = some (.unenumerated oldNode oldScs) := by
      rw [frame.values, ← foundTarget]
      exact oldStored
    have adapted : ∀ extraIndex,
        SourcePruningEnumerationIncomingCacheAdapter.adapt afterCaller.checked.native.machine.heap
          (incomingK + extraIndex) winner incomingScs folded read
          (if replacement = .empty then [] else [.ok ((), after.core)]) = some after := by
      intro extraIndex
      by_cases empty : replacement = .empty
      ·
        have handleZero : handle = 0 := by
          simpa only [empty, encodeNode, Option.some.injEq] using encoded.symm
        simp only [ite_eq_left empty, SourcePruningEnumerationIncomingCacheAdapter.adapt, readStored]
        simpa only [handleZero, afterSame] using cacheRun extraIndex
      · simp only [ite_eq_right empty, SourcePruningEnumerationIncomingCacheAdapter.adapt,
          afterStored, Option.bind_some]
        exact cacheRun extraIndex
    have resultFrame : ∀ (slot : Nat), slot ∉ recorded →
        after.core.values[slot]? = before.core.values[slot]? := by
      intro slot outside
      have different : slot ≠ winner := fun same => outside (same ▸ winnerMember)
      simpa only [afterSame, List.getElem?_set_ne (Ne.symm different), frame.values] using
        foldedFrame slot outside
    have resultSafe : Safe after.core := by
      refine ⟨afterStorage, ?_⟩
      intro slot value stored
      by_cases same : slot = winner
      · subst slot
        have valueSame : value = .unenumerated (some handle) (incomingScs ++ oldScs) :=
          Option.some.inj (stored.symm.trans afterStored)
        have root : IsRoot after.core.representatives winner :=
          (root_iff _ _ afterPaths winner).mpr ((root_iff _ _ foldPaths winner).mp foldedRoot)
        exact ⟨fun _ => root, fun _ => by simp only [valueSame, ne_eq, reduceCtorEq, not_false_eq_true]⟩
      · have oldStored : folded.core.values[slot]? = some value := by
          simpa only [afterSame, List.getElem?_set_ne (Ne.symm same), frame.values] using stored
        exact ((foldedSafe rfl).2 slot value oldStored).trans
          ((root_iff _ _ foldPaths slot).trans (root_iff _ _ afterPaths slot).symm)
    have resultOrigin : ∀ (slot : Nat) (fragment : Fragments.Fragment Symbol),
        after.core.values[slot]? = some (.enumerated fragment) →
        before.core.values[slot]? = some (.enumerated fragment) := by
      intro slot fragment stored
      by_cases same : slot = winner
      · subst slot
        rw [afterStored] at stored
        cases stored
      · apply foldedOrigin slot fragment
        simpa only [afterSame, List.getElem?_set_ne (Ne.symm same), frame.values] using stored
    refine ⟨r, n, p, h, incomingK, recorded, winner, joined, [((), folded)], foldCaller,
      foldQueries, foldFinal, foldInventory, folded, raw, afterCaller, outer, savedQueries,
      final, next, after, prefixRun, recordedSame, winnerMember, movedSame, joinedSame,
      joinedFlagsSame, prefixRoots, prefixCounts, joinedFlags, cachedFoldRun, foldRun,
      .inr rfl, foldPost, foldQuerySame, foldCounter, foldForest, foldPaths, foldStorage,
      foldRealized, foldedRoot, foldPending, foldCounts, foldWaiting, foldFlags, foldEliminated,
      foldCompleted, foldedFrame, foldedSafe, foldedOrigin, terminalRun, post, querySame, ?_,
      (by simpa only [congrArg EnumerationState.State.counter joinedSame] using afterCounter.trans foldCounter),
      afterPaths, afterStorage, afterRealized, afterCounts, afterFlags, resultFrame,
      (fun _ => resultSafe),
      (protects before.core after.core roots first rest recorded winner paths recordedSame
        winnerMember afterPaths resultFrame), resultOrigin, ?_, ?_, rejectedBranch, ?_⟩
    · intro extraRepresentative extraNative P H extraIndex enoughP enoughH
      rw [outerRead, rawSame]
      simp only [run, ite_eq_right nonempty, prefixRun extraRepresentative,
        ← joinedFlagsSame, cachedFoldRun extraNative P H enoughP enoughH,
        List.map_cons, List.map_nil, SourcePruningEnumerationIncomingCacheAdapter.run,
        EnumerationExpandableIndex.frame,
        incomingRun extraRepresentative extraNative P H enoughP enoughH,
        adapted extraIndex]
      simp only [apply_ite, List.map_nil, List.map_cons]
    · intro allowed valid inputs
      exact SourcePruningEnumerationNativeReferences.incoming_written allowed read after.core winner handle oldNode
        incomingScs oldScs (by simpa only [EnumerationReferences.ReferencesAllowed, frame.values] using
          (foldAllowed allowed valid)) inputs readStored
        (by rw [afterSame])
    · simp
    · intro isCompleted
      exact ⟨incomingK, oldNode, oldScs, read, after, replacement, handle, rfl, outerRead,
        reading, frame, incomingRun, writePrefix, afterSame, afterStored, afterStorage,
        afterRealized, incomingPost, unfolding, cacheRun, afterCounter, afterRepresentatives,
        afterPaths, afterCounts, writeWaiting, afterFlags, afterExpandable, rawSame,
        winnerBound, replacementAvailable, replacementClosed, encoded, decoded, optional, present⟩

end MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
