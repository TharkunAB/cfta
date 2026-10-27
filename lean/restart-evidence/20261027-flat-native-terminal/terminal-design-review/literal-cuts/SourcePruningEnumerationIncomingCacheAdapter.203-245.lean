  obtain ⟨r, n, p, h, k, oldNode, oldScs, read, afterCaller, savedQueries, final, next,
    replacement, handle, after, reading, frame, originalRun, writePrefix, afterSame, afterStored,
    afterStorage, afterRealized, post, querySame, unfolding, replacementAvailable,
    replacementClosed, encoded, decoded, cacheRun, afterCounter, afterRepresentatives,
    afterPaths, afterCounts, waiting, flagsAfter, expandableAfter, optional, present⟩ :=
      SourcePruningEnumerationCachedIncoming.complete formulas solver inventory beforeCaller before
        checkEmpty target incoming incomingScs memos roots initial storage realized paths counts flags
        root pending available closed bounded ranges
  obtain ⟨found, lookup, oldStored, _readSame⟩ :=
    (getValue_success r target before.core read (.unenumerated oldNode oldScs)).mp (by
      unfold Success
      rw [show ExceptT.run (getValue r target before.core) =
        [.ok (.unenumerated oldNode oldScs, read)] from
          by simpa only [Nat.add_zero] using reading 0]
      exact List.mem_singleton_self _)
  have foundTarget : found.representative = target := by
    obtain ⟨rootSize, rootPath⟩ := root
    exact (UnionFind.reaches_unique
      (UnionFind.findRoot_correct r before.core.representatives target found lookup).1 rootPath).1
  have readStored : read.values[target]? = some (.unenumerated oldNode oldScs) := by
    rw [frame.values, ← foundTarget]
    exact oldStored
  have adapted : ∀ extraIndex,
      adapt afterCaller.checked.native.machine.heap (k + extraIndex) target incomingScs before read
        (if replacement = .empty then [] else [.ok ((), after.core)]) = some after := by
    intro extraIndex
    by_cases empty : replacement = .empty
    ·
      have handleZero : handle = 0 := by
        simpa only [empty, encodeNode, Option.some.injEq] using encoded.symm
      simp only [ite_eq_left empty, adapt, readStored]
      simpa only [handleZero, afterSame] using cacheRun extraIndex
    · simp only [ite_eq_right empty, adapt, afterStored, Option.bind_some]
      exact cacheRun extraIndex
  refine ⟨r, n, p, h, k, oldNode, oldScs, read, afterCaller, savedQueries, final, next,
    replacement, handle, after, reading, frame, originalRun, writePrefix, afterSame, afterStored,
    afterStorage, afterRealized, post, querySame, unfolding, replacementAvailable,
    replacementClosed, encoded, decoded, cacheRun, adapted, ?_, afterCounter, afterRepresentatives,
    afterPaths, afterCounts, waiting, flagsAfter, expandableAfter, optional, present⟩
  intro extra extraNative P H extraIndex enoughP enoughH
  simp only [run, originalRun extra extraNative P H enoughP enoughH, adapted extraIndex]

end MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter
