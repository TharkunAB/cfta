                afterCaller = SourceCurrentAllocatedPartialState.advance foldCaller queried foldCaller.fourth foldCaller.merge ∧
                final = foldFinal)))) ∧
      (∀ extraNative P H, p ≤ P → h ≤ H →
        ∃ flatRows flatOuter recovered,
          run checkEmpty (n + extraNative) P H first rest beforeCaller flat incoming incomingScs memos.query =
            ((.ok (some flatRows), afterCaller, savedQueries, flatOuter, joined.waiting), some recovered) ∧
          EnumerationFlatCached.Related recovered resultCache ∧
          EnumerationFlatState.Related flatOuter outer ∧
          EnumerationResultRelation.Results EnumerationFlatState.Related flatRows raw ∧
          EnumerationFlatNativeIndex.Correct afterCaller.checked.native.machine.heap recovered) := by
  obtain ⟨r, n, p, h, k, recorded, winner, joined, foldRows, foldCaller, foldQueries,
    foldFinal, foldInventory, folded, raw, afterCaller, outer, savedQueries, final, next, resultCache, packet⟩ :=
    SourcePruningEnumerationCachedTerminalAdapter.complete formulas solver inventory beforeCaller before
      checkEmpty first rest incoming incomingScs roots memos initial safe paths counts flags bounded pending
      realized nonempty available closed incomingBounded ranges
  refine ⟨r, n, p, h, k, recorded, winner, joined, foldRows, foldCaller, foldQueries,
    foldFinal, foldInventory, folded, raw, afterCaller, outer, savedQueries, final, next, resultCache, packet, ?_⟩
  rcases packet with ⟨prefixRun, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, stable, _, resultPaths, resultStorage, _, resultCounts, resultFlags, _⟩
  intro extraNative P H enoughP enoughH
  obtain ⟨flatRows, flatOuter, recovered, actual, relatedCache, relatedOuter, relatedRows⟩ :=
    observed related first rest r recorded winner joined.waiting joined.core prefixRun
      checkEmpty (n + extraNative) P H k beforeCaller afterCaller incoming incomingScs memos.query savedQueries
      raw outer resultCache (fun extraRepresentative extraIndex =>
        stable extraRepresentative extraNative P H extraIndex enoughP enoughH)
  exact ⟨flatRows, flatOuter, recovered, actual, relatedCache, relatedOuter, relatedRows,
    EnumerationFlatNativeIndex.correct_of_related relatedCache afterCaller.checked.native.machine.heap
      (EnumerationCanonicalUnion.mergedRoots roots recorded winner) resultPaths resultStorage.aligned
      resultFlags resultCounts⟩

end MicroCFTA.EnumerationFlatNativeTerminal
