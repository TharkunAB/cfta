          have old := headOrigin held storedFragment stored
          exact (protects held storedFragment old).avoids retained (childPending held storedFragment old)
        have tailReservation : Reserved bits (advance seed (bucket.length + 1)) (cost rest) :=
          reserved.after_prefix
        obtain ⟨tailR, tailN, tailP, tailH, tailK, tailFragments, afterCaller, after, savedQueries,
          final, next, afterRoots, tailResult, tailRun, tailPost, querySame, tailGrowth, afterPaths,
          storage, afterRealized, afterCounts, afterFlags, tailOrigin, tailProtected, tailRootsProtected,
          tailReferences, tailPending, tailBounds, tailShape, tailFits, tailKnown, tailCarriersObserver⟩ :=
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
          (fun valid => tailPending (headPending valid)), ?_, ?_, finalFits, finalKnown, ?_⟩
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
              ((n + tailN) + en) P H ((k + tailK) + ek) rest middleCaller middle middleQueries = tailResult := by
            simpa only [headQueries, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail
          simp only [SourcePruningEnumerationChildTraversal.run, headExact, tailExact, result]
          cases tailResult <;> rfl
        · intro held storedFragment stored
          have first := protects held storedFragment stored
          have middleStored : middle.core.values[held]? = some (.enumerated storedFragment) := first.value.trans stored
          exact first.trans (tailProtected held storedFragment middleStored)
        · intro held inside root avoids
          have first := headProtected held inside root (avoids incoming bucket (by simp))
          apply first.trans
          apply tailRootsProtected held (Nat.lt_of_lt_of_le inside growth) first.root
          intro value retained member
          exact first.avoids retained (avoids value retained (List.mem_cons_of_mem _ member))
        · intro allowed valid allowedInputs
          apply tailReferences allowed
            (headReferences allowed valid (allowedInputs incoming bucket (by simp)))
          intro value retained member
          exact allowedInputs value retained (List.mem_cons_of_mem _ member)
        · intro child member
          rcases List.mem_cons.mp member with rfl | member
          · exact fragmentBound_mono _ _ tailGrowth _ fragmentBound
          · exact tailBounds child member
        · rcases tailShape with ⟨completed, afterSafe, fragmentHistory⟩ | ⟨outer, waiting, stopped⟩
          · subst tailResult
            refine .inl ⟨rfl, afterSafe, ?_⟩
            intro child member
            rcases List.mem_cons.mp member with rfl | member
            · refine ⟨pendingFragment_preserved middle.core after.core middleSafe afterSafe tailGrowth
                child fragmentBound fragmentPending tailOrigin tailProtected, ?_⟩
              intro held inside root avoids
              have first := headProtected held inside root (avoids incoming bucket (by simp))
              have last := tailRootsProtected held (Nat.lt_of_lt_of_le inside growth) first.root (by
                intro value retained member
                exact first.avoids retained (avoids value retained (List.mem_cons_of_mem _ member)))
              exact (fragmentAvoid_classes middle.core.representatives after.core.representatives held child
                last.classes).mpr (fragmentSeparate held inside root (avoids incoming bucket (by simp)))
            · obtain ⟨childPending, childSeparate⟩ := fragmentHistory child member
              refine ⟨childPending, ?_⟩
              intro held inside root avoids
              have first := headProtected held inside root (avoids incoming bucket (by simp))
              apply childSeparate held (Nat.lt_of_lt_of_le inside growth) first.root
              intro value retained member
              exact first.avoids retained (avoids value retained (List.mem_cons_of_mem _ member))
          · subst tailResult
            exact .inr ⟨outer, waiting, rfl⟩

        · intro carried
          have actual := headRun 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
          simp only [Nat.add_zero, singleton] at actual
          have headCarriers := SourcePruningEnumerationChildDispatch.successful_carriers safe carried actual
          obtain ⟨lastCarriers, lastReferences, lastFragments⟩ :=
            tailCarriersObserver headCarriers.2.2.1
          refine ⟨headCarriers.2.1.trans lastCarriers, lastReferences, ?_⟩
          intro child member
          rcases List.mem_cons.mp member with rfl | member
          · exact headCarriers.2.2.2.preserve child lastCarriers
          · exact lastFragments child member

end MicroCFTA.SourcePruningEnumerationTraversalCompletion
