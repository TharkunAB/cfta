  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  have inherited : EnumerationSemantics.ValidSuspended scs := canonical _ (List.mem_of_getElem? stored)
  have avoids := ready.avoids handle scs stored
  obtain ⟨r0, n0, p0, h0, k0, reachedCaller, middle, queries0, _final, _next, middleRoots, result,
    edgeRun, _post, _querySame, _growth, middlePaths, middleStorage, middleRealized, middleCounts,
    middleFlags, _origin, _retained, protects, _pendingHistory, _incomingHistory, shape⟩ :=
    SourcePruningEnumerationSelectedEdge.complete_with_fragments formulas solver inventory caller before checkEmpty
      parentEntry edges depth free edge scs roots memos initial available closed selected ready.safe realized
      paths counts flags bounded pending allowed tries residual projected ranges
  rcases shape with ⟨produced, completed, middleSafe, fragmentBound, _fragmentPending, _fragmentSeparate⟩ |
    ⟨fragments, outer, waiting, stopped⟩
  · subst result
    have frame := protects uv ready.inside ready.root avoids
    have currentStored : middle.core.values[uv]? = some (.unenumerated (some handle) scs) :=
      frame.value.trans stored
    obtain ⟨finishFuel, finished, finishRun, _raw, written, _finalStored, _finalFlag, _finalWaiting,
      _afterPaths, _afterCounts, _afterFlags, _afterStorage, _afterRealized, _safeFinish⟩ :=
      SourcePruningEnumerationFinalize.complete reachedCaller.checked.native.machine.heap middle uv produced
        (.unenumerated (some handle) scs) currentStored middleRoots middlePaths middleCounts middleFlags
        middleStorage fragmentBound middleRealized
    have canonicalRun : run checkEmpty (r + r0) (n + n0) (max p p0) (max h h0)
        (k + (k0 + finishFuel)) uv scs edge caller before memos.query =
        some (.complete produced reachedCaller queries0 finished) := by
      have selectedRun : SourcePruningEnumerationSelectedEdge.run checkEmpty
          (r + r0) (n + n0) (max p p0) (max h h0) (k + (k0 + finishFuel))
          scs edge caller before memos.query = .complete produced reachedCaller queries0 middle := by
