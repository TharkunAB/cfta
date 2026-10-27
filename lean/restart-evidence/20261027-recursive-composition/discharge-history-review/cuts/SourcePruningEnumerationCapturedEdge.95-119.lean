  obtain ⟨value, lookup, available, closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry edges depth free := Option.some.inj (lookup.symm.trans decoded)
  subst value
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  have avoids := ready.avoids handle scs stored
  obtain ⟨r, n, p, h, k, afterCaller, middle, savedQueries, final, next, afterRoots, edgeResult,
    edgeRun, post, querySame, growth, middlePaths, storage, middleRealized, middleCounts,
    middleFlags, origin, retained, protects, pendingHistory, incomingHistory, shape⟩ :=
    SourcePruningEnumerationSelectedEdge.complete_with_fragments formulas solver inventory caller before checkEmpty
      parentEntry edges depth free edge scs roots memos initial available closed selected ready.safe realized
      paths counts flags bounded pending allowed tries residual projected ranges
  rcases shape with ⟨fragment, completed, middleSafe, fragmentBound, fragmentPending, fragmentSeparate⟩ |
    ⟨fragments, outer, waiting, stopped⟩
  · subst edgeResult
    have frame := protects uv ready.inside ready.root avoids
    have currentStored : middle.core.values[uv]? = some (.unenumerated (some handle) scs) :=
      frame.value.trans stored
    obtain ⟨fuel, after, finishRun, _raw, core, finalStored, _finalFlag, _finalWaiting,
      afterPaths, afterCounts, afterFlags, afterStorage, afterRealized, safeFinish⟩ :=
      SourcePruningEnumerationFinalize.complete afterCaller.checked.native.machine.heap middle uv fragment
        (.unenumerated (some handle) scs) currentStored afterRoots middlePaths middleCounts middleFlags
        storage fragmentBound middleRealized
    have afterSafe := safeFinish middleSafe frame.root
    have separate := fragmentSeparate uv ready.inside ready.root avoids
