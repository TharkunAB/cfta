      (fun input => (input.1, input.2.1))) = inputs := by
    simp only [List.map_map]
    exact List.map_id _
  have numeric : SourcePruningEnumerationTraversalCompletion.Ranges checkEmpty inputs caller own memos.query := by
    have admitted := ranges edge.entry.key.symbol _ residual own ownRun
    rwa [readback] at admitted
  obtain ⟨childR, childN, childP, childH, childK, childFragments, reachedCaller,
    reached, childQueries, _childMemos, _childInventory, _childRoots, childResult,
    childrenRun, _post, _querySame, _growth, _afterPaths, _storage, _afterRealized,
    _afterCounts, _afterFlags, _origin, _enumProtects, _rootsProtects, _references,
    _pendingHistory, _fragmentBounds, shape, _childMeaning⟩ :=
    SourcePruningEnumerationTraversalCompletion.complete_with_fragments_semantics
      formulas solver inventory caller own checkEmpty inputs roots memos
      initial ownSafe ownPaths ownCounts ownFlags ownRealized genuine numeric
  have commonRun := observed childR childN (max p childP) (max h childH) childK
    (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have childrenAt : SourcePruningEnumerationChildTraversal.run checkEmpty
