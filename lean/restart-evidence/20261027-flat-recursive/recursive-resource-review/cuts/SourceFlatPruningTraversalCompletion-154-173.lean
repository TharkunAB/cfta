          intro held storedFragment stored
          have old := headOrigin held storedFragment stored
          exact (protects held storedFragment old).avoids retained (childPending held storedFragment old)
        have firstRun := headRun 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
        simp only [Nat.add_zero, singleton] at firstRun
        have tailRanges : Ranges checkEmpty rest middleCaller middle middleMemos.query := by
          rw [headQueries]
          exact ranges.2 r n p h k fragment middleCaller middle middleQueries outer waiting firstRun
        obtain ⟨tailR, tailN, tailP, tailH, tailK, tailFragments, afterCaller, after, savedQueries,
          final, next, afterRoots, tailResult, tailRun, tailPost, querySame, tailGrowth, afterPaths,
          storage, afterRealized, afterCounts, afterFlags, tailOrigin, tailProtected, tailRootsProtected,
          tailReferences, tailPending, tailBounds, tailShape, tailFlat⟩ :=
          ih middleInventory middleCaller middle middleRoots middleMemos headPost.context middleSafe
            middlePaths middleCounts middleFlags middleRealized tailGenuine tailRanges
        let result : SourcePruningEnumerationChildTraversal.Result width := match tailResult with
          | .complete fragments caller queries cache => .complete (fragment :: fragments) caller queries cache
          | .stopped fragments observation candidate => .stopped (fragment :: fragments) observation candidate
        refine ⟨r + tailR, n + tailN, max p tailP, max h tailH, k + tailK,
          fragment :: tailFragments, afterCaller, after, savedQueries, final, next, afterRoots, result,
          ?_, headPost.trans tailPost, querySame, Nat.le_trans growth tailGrowth, afterPaths,
