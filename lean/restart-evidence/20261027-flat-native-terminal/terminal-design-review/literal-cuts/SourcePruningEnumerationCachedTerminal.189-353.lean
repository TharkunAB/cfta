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
          exact stored
        constructor
        · intro live
          have originalRoot := (safe.2 slot value originalStored).mp live
          have fixed := (root_iff _ roots paths slot).mp originalRoot
          apply (root_iff _ _ foldPaths slot).mpr
          simp only [EnumerationCanonicalUnion.mergedRoots, fixed, ite_eq_right selected]
        · intro root
          have named := (root_iff _ _ foldPaths slot).mp root
          by_cases namedSelected : roots slot ∈ recorded
          · simp only [EnumerationCanonicalUnion.mergedRoots, ite_eq_left namedSelected] at named
            exact (atWinner named.symm).elim
          · have fixed : roots slot = slot := by
              simpa only [EnumerationCanonicalUnion.mergedRoots, ite_eq_right namedSelected] using named
            exact (safe.2 slot value originalStored).mpr ((root_iff _ roots paths slot).mpr fixed)
  have foldedOrigin : ∀ (slot : Nat) (fragment : Fragments.Fragment Symbol),
      folded.core.values[slot]? = some (.enumerated fragment) →
      before.core.values[slot]? = some (.enumerated fragment) := by
    intro slot fragment stored
    have original : joined.values[slot]? = some (.enumerated fragment) := foldOrigin slot fragment stored
    rw [joinedSame] at original
    exact original
  rcases foldShape with rejected | completed
  · subst foldRows
    refine ⟨prefixFuel, foldFuel, foldP, foldH, recorded, winner, joinedCache, [],
      foldCaller, foldQueries, foldFinal, foldInventory, folded, [], foldCaller, folded.core,
      foldQueries, foldFinal, foldInventory, prefixRun, recordedSame, winnerMember, movedSame,
      joinedSame, rfl, prefixRoots, prefixCounts, joinedFlags, cachedFoldRun, foldRun, .inl rfl,
      foldPost, foldQuerySame, foldCounter, foldForest, foldPaths, foldStorage, foldRealized,
      foldedRoot, foldPending, foldCounts, foldWaiting, foldFlags, foldEliminated, foldCompleted,
      foldedFrame, foldedSafe, foldedOrigin,
      ?_, foldPost, foldQuerySame, ?_, ?_⟩
    · intro extraRepresentative extraNative P H enoughP enoughH
      simp only [SourcePruningEnumerationTerminal.run, ite_eq_right nonempty,
        prefixRun extraRepresentative, foldRun extraNative P H enoughP enoughH, List.map_nil, joinedCache]
    · intro isRejected
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro isCompleted
      cases isCompleted
  · subst foldRows
    have foldedAvailable : Available foldCaller.checked.native.machine.heap incoming := by
      exact foldPost.effects.keeps.available incoming available
    have foldedBounded : ∀ sc ∈ incomingScs, sc.var < folded.core.counter := by
      intro sc member
      rw [foldCounter]
      change sc.var < joined.counter
      simpa only [congrArg EnumerationState.State.counter joinedSame] using incomingBounded sc member
    obtain ⟨incomingR, incomingN, incomingP, incomingH, k, oldNode, oldScs, read, afterCaller,
      savedQueries, final, next, replacement, handle, after, reading, frame, incomingRun,
      writePrefix, afterSame, afterStored, afterStorage, afterRealized, incomingPost,
      incomingQuerySame, unfolding, replacementAvailable, replacementClosed, encoded, decoded,
      cacheRun, afterCounter, afterRepresentatives, afterPaths, afterCounts, incomingWaiting,
      afterFlags, afterExpandable, optional, present⟩ :=
      SourcePruningEnumerationCachedIncoming.complete formulas solver foldInventory foldCaller
        folded checkEmpty winner incoming incomingScs foldFinal
        (EnumerationCanonicalUnion.mergedRoots roots recorded winner) foldPost.context foldStorage
        foldRealized foldPaths foldCounts foldFlags foldedRoot foldPending foldedAvailable closed
        foldedBounded ((ranges prefixFuel recorded winner moved joined
          (by simpa only [Nat.add_zero] using prefixRun 0)).2 foldFuel foldP foldH foldCaller
            folded.core foldQueries (by
              simpa only [Nat.add_zero, List.map_cons, List.map_nil] using
                foldRun 0 foldP foldH (by omega) (by omega)))
    have writeWaiting : after.waiting = EnumerationCanonicalWaiting.count
        (EnumerationCanonicalUnion.mergedRoots roots recorded winner) 1 incomingScs moved := by
      simpa only [foldWaiting] using incomingWaiting
    have winnerBound : winner < after.core.counter := by
      rw [afterStorage.aligned]
      exact (List.getElem?_eq_some_iff.mp afterStored).elim (fun inside _elementEquality => inside)
    simp only [foldQuerySame] at incomingRun optional
    refine ⟨prefixFuel + incomingR, foldFuel + incomingN, foldP + incomingP, foldH + incomingH,
      recorded, winner, joinedCache, [((), folded)], foldCaller, foldQueries, foldFinal,
      foldInventory, folded, (if replacement = .empty then [] else [.ok (.hole winner, after.core)]),
      afterCaller, read, savedQueries, final, next, ?_, recordedSame, winnerMember, movedSame,
      joinedSame, rfl, prefixRoots, prefixCounts, joinedFlags, ?_, ?_, .inr rfl, foldPost,
      foldQuerySame, foldCounter, foldForest, foldPaths, foldStorage, foldRealized, foldedRoot,
      foldPending, foldCounts, foldWaiting, foldFlags, foldEliminated, foldCompleted,
      foldedFrame, foldedSafe, foldedOrigin, ?_,
      foldPost.trans incomingPost, incomingQuerySame, ?_, ?_⟩
    · intro extra
      simpa only [Nat.add_assoc] using prefixRun (incomingR + extra)
    · intro extra P H enoughP enoughH
      simpa only [Nat.add_assoc] using
        cachedFoldRun (incomingN + extra) P H (by omega) (by omega)
    · intro extra P H enoughP enoughH
      simpa only [Nat.add_assoc] using foldRun (incomingN + extra) P H (by omega) (by omega)
    · intro extraRepresentative extraNative P H enoughP enoughH
      simp only [SourcePruningEnumerationTerminal.run, ite_eq_right nonempty, Nat.add_assoc,
        prefixRun (incomingR + extraRepresentative),
        foldRun (incomingN + extraNative) P H (by omega) (by omega), List.map_cons, List.map_nil, joinedCache]
      rw [Nat.add_left_comm prefixFuel incomingR extraRepresentative,
        Nat.add_left_comm foldFuel incomingN extraNative,
        incomingRun (prefixFuel + extraRepresentative) (foldFuel + extraNative) P H (by omega) (by omega)]
      by_cases empty : replacement = .empty <;> simp [empty]
    · intro isRejected
      cases isRejected
    · intro isCompleted
      refine ⟨k, oldNode, oldScs, read, after, replacement, handle, rfl, ?_, frame, ?_,
        writePrefix, afterSame, afterStored, afterStorage, afterRealized, incomingPost,
        unfolding, cacheRun, afterCounter, afterRepresentatives, afterPaths, afterCounts,
        writeWaiting, afterFlags, afterExpandable, rfl, winnerBound, replacementAvailable,
        replacementClosed, encoded, decoded, optional, present⟩
      · intro extra
        simpa only [Nat.add_assoc, Nat.add_left_comm prefixFuel incomingR extra] using
          reading (prefixFuel + extra)
      · intro extraRepresentative extraNative P H enoughP enoughH
        simpa only [Nat.add_assoc, Nat.add_left_comm prefixFuel incomingR extraRepresentative,
          Nat.add_left_comm foldFuel incomingN extraNative] using
          incomingRun (prefixFuel + extraRepresentative) (foldFuel + extraNative) P H (by omega) (by omega)

end MicroCFTA.SourcePruningEnumerationCachedTerminal
