            (∀ sc ∈ bucket, sc.var < middle.core.counter) ∧ InputsPending middle.core bucket := by
          intro value retained member
          obtain ⟨childAvailable, childClosed, childBounded, childPending⟩ :=
            genuine value retained (List.mem_cons_of_mem _ member)
          refine ⟨headPost.effects.keeps.available value childAvailable, childClosed,
            fun sc member => Nat.lt_of_lt_of_le (childBounded sc member) growth, ?_⟩
          intro held storedFragment stored
          have old := headOrigin held storedFragment stored
          exact (protects held storedFragment old).avoids retained (childPending held storedFragment old)
        have tailReservation : Reserved bits (advance seed (bucket.length + 1)) (cost rest) :=
          reserved.after_prefix
        obtain ⟨tailR, tailN, tailP, tailH, tailK, tailFragments, afterCaller, after, savedQueries,
          final, next, afterRoots, tailResult, tailRun, tailPost, querySame, tailGrowth, afterPaths,
          storage, afterRealized, afterCounts, afterFlags, tailOrigin, tailProtected, tailRootsProtected,
          tailReferences, tailPending, tailBounds, tailShape, tailFits, tailKnown⟩ :=
          ih (advance seed (bucket.length + 1)) middleInventory middleCaller middle middleRoots middleMemos headPost.context middleSafe
            middlePaths middleCounts middleFlags middleRealized tailGenuine middleFits tailReservation middleKnown
        have finalFits : Fits (advance seed (cost ((incoming, bucket) :: rest))).2 afterCaller.checked := by
          change Fits (advance seed ((bucket.length + 1) + cost rest)).2 afterCaller.checked
          rw [SourcePruningEnumerationIncomingReservation.advance_add]
          exact tailFits
        have finalKnown : Heap (fun guard => guard ∈ (advance seed (cost ((incoming, bucket) :: rest))).1)
            afterCaller.checked.native.machine.heap := by
          change Heap (fun guard => guard ∈ (advance seed ((bucket.length + 1) + cost rest)).1)
            afterCaller.checked.native.machine.heap
          rw [SourcePruningEnumerationIncomingReservation.advance_add]
          exact tailKnown
        let result : SourcePruningEnumerationChildTraversal.Result (bits + 2) := match tailResult with
          | .complete fragments caller queries cache => .complete (fragment :: fragments) caller queries cache
          | .stopped fragments observation candidate => .stopped (fragment :: fragments) observation candidate
        refine ⟨r + tailR, n + tailN, max p tailP, max h tailH, k + tailK,
          fragment :: tailFragments, afterCaller, after, savedQueries, final, next, afterRoots, result,
          ?_, headPost.trans tailPost, querySame, Nat.le_trans growth tailGrowth, afterPaths,
          storage, afterRealized, afterCounts, afterFlags, headOrigin.trans tailOrigin, ?_, ?_, ?_,
          (fun valid => tailPending (headPending valid)), ?_, ?_, finalFits, finalKnown⟩
        · intro er en P H ek largeP largeH
          have head := headRun (tailR + er) (tailN + en) P H (tailK + ek)
            (Nat.le_trans (Nat.le_max_left _ _) largeP) (Nat.le_trans (Nat.le_max_left _ _) largeH)
          have tail := tailRun (r + er) (n + en) P H (k + ek)
            (Nat.le_trans (Nat.le_max_right _ _) largeP) (Nat.le_trans (Nat.le_max_right _ _) largeH)
          have headExact : SourcePruningEnumerationChildDispatch.run checkEmpty ((r + tailR) + er)
              ((n + tailN) + en) P H ((k + tailK) + ek) bucket incoming beforeCaller before memos.query =
              ((.ok (some [.ok (fragment, middle.core)]), middleCaller, middleQueries, outer, waiting), some middle) := by
            simpa only [Nat.add_assoc, singleton] using head
          have tailExact : SourcePruningEnumerationChildTraversal.run checkEmpty ((r + tailR) + er)
