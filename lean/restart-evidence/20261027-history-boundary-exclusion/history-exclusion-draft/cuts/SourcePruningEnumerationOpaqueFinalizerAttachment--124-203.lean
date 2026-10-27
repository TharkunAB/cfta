    eventAdmission metadata ownPacket bound prefixFragments eventCaller eventBefore eventQueries prefixTrace
  obtain ⟨available, closed, _eventBounded, _eventPending⟩ :=
    remainingGenuine value bucket (by simp)
  have suffixGenuine : ∀ incoming retained, (incoming, retained) ∈ suffix →
      Available eventCaller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
      (∀ sc ∈ retained, sc.var < eventBefore.core.counter) ∧ InputsPending eventBefore.core retained := by
    intro incoming retained member
    exact remainingGenuine incoming retained (List.mem_cons_of_mem _ member)
  have suffixReserved : Reserved bits (advance seed (cost consumed)) (cost suffix) :=
    eventReserved.prefix (by change cost suffix ≤ bucket.length + 1 + cost suffix; omega)
  obtain ⟨opaqueHandle, sr, sn, sp, sh, sk, suffixResultFragments, suffixCaller, suffixCache,
    suffixQueries, _suffixMemos, _suffixInventory, _suffixRoots, suffixResult,
    _encoded, lookup, _opaqueCore, suffixFull, _suffixIsolated, finalizerIsolated⟩ :=
    EnumerationDischargeHistory.opaque_suffix_complete_isolated_resources
      (advance seed (cost consumed)) formulas solver eventInventory eventCaller eventMemos metadata
      eventBefore opaqueAfter value bucket W eventPacket available closed boundary nonterminal opaqueRow
      checkEmpty suffix suffixGenuine eventFits suffixReserved eventKnown
  obtain ⟨suffixRunning, suffixPost, _suffixQuery, _suffixGrowth, _suffixPaths, _suffixStorage,
    _suffixRealized, _suffixCounts, _suffixFlags, _suffixOrigin, _suffixExpandedProtected,
    _suffixRootsProtected, _suffixReferences, _suffixPending, _suffixBounds, suffixShape,
    _suffixFits, _suffixKnown⟩ := suffixFull
  let padding := sr + sn + sp + sh + sk
  let nextWork := B + bound + padding
  have nextHead : SourcePruningEnumerationCapturedEdge.run checkEmpty nextWork nextWork nextWork nextWork
      nextWork uv scs edge caller before memos.query = some (.complete fragment reached saved headCache) := by
    simpa only [nextWork, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using head.running (B + padding)
  obtain ⟨nextPrefixFragments, nextSuffixFragments, nextEventCaller, nextEventBefore, nextOpaqueAfter,
    nextChildCache, nextEventQueries, _nextHandle, _nextFragmentShape, nextPrefixTrace,
    _nextObservation, nextOpaqueRow, _nextEncoded, _nextAllocated, nextSuffixTrace, nextFinalized⟩ :=
    captured_opaque_event checkEmpty nextWork nextWork nextWork nextWork nextWork uv scs edge caller reached
      before own headCache memos.query saved edge.entry.key.symbol staged residual fragment consumed suffix
      value bucket ownRun (stagedInputs.trans location) boundary nonterminal nextHead
  have nextPrefixFixed : prefixResult =
      .complete nextPrefixFragments nextEventCaller nextEventQueries nextEventBefore := by
    have canonical : SourcePruningEnumerationChildTraversal.run checkEmpty nextWork nextWork nextWork
        nextWork nextWork consumed caller own memos.query = prefixResult := by
      simpa only [nextWork, B, Nat.add_assoc] using prefixRunning (bound + padding)
    have actual := SourcePruningEnumerationChildTraversal.trace_complete nextPrefixTrace
    exact canonical.symm.trans actual
  have prefixSame := SourcePruningEnumerationChildTraversal.Result.complete.inj
    (prefixFixed.symm.trans nextPrefixFixed)
  obtain ⟨fragmentsSame, callerSame, queriesSame, cacheSame⟩ := prefixSame
  subst nextPrefixFragments nextEventCaller nextEventQueries nextEventBefore
  have sameOpaque : opaqueAfter = nextOpaqueAfter := by
    have canonical := (opaque_prepare_fuel eventCaller.checked.native.machine.heap W nextWork bucket value
      eventBefore boundary).symm.trans opaqueRow
    exact (Prod.mk.inj (List.cons.inj (Option.some.inj (canonical.symm.trans nextOpaqueRow))).1).2
  subst nextOpaqueAfter
  have sufficient : sr ≤ nextWork ∧ sn ≤ nextWork ∧ sp ≤ nextWork ∧ sh ≤ nextWork ∧ sk ≤ nextWork := by
    dsimp only [nextWork, padding]
    omega
  have actualSuffix : SourcePruningEnumerationChildTraversal.run checkEmpty nextWork nextWork nextWork
      nextWork nextWork suffix eventCaller opaqueAfter eventMemos.query =
      .complete nextSuffixFragments reached saved nextChildCache := by
    simpa only [eventQuery] using SourcePruningEnumerationChildTraversal.trace_complete nextSuffixTrace
  have canonicalSuffix : SourcePruningEnumerationChildTraversal.run checkEmpty nextWork nextWork nextWork
      nextWork nextWork suffix eventCaller opaqueAfter eventMemos.query = suffixResult := by
    have canonical := suffixRunning (nextWork - sr) (nextWork - sn) nextWork nextWork (nextWork - sk)
      (by omega) (by omega)
    have rSame : sr + (nextWork - sr) = nextWork := by omega
    have nSame : sn + (nextWork - sn) = nextWork := by omega
    have kSame : sk + (nextWork - sk) = nextWork := by omega
    simpa only [rSame, nSame, kSame] using canonical
  have suffixSame := canonicalSuffix.symm.trans actualSuffix
  rcases suffixShape with ⟨suffixComplete, _suffixSafe, _suffixHistory⟩ | ⟨outer, waiting, suffixStopped⟩
  · rw [suffixComplete] at suffixSame
    have endpoints := SourcePruningEnumerationChildTraversal.Result.complete.inj suffixSame
    obtain ⟨fragmentsSame, callerSame, queriesSame, cacheSame⟩ := endpoints
    subst nextSuffixFragments suffixCaller suffixQueries nextChildCache
    have different : uv ≠ eventBefore.core.counter := by
      have inside := head.admission.ready.inside
      omega
    refine ⟨eventBefore.core.counter, opaqueHandle, ?_, ?_⟩
    · exact lookupNode_keeps eventCaller.checked.native.machine.heap reached.checked.native.machine.heap
        suffixPost.effects.keeps opaqueHandle value lookup
    · exact finalizerIsolated residual fragment nextWork uv headCache different nextFinalized
  · rw [suffixStopped] at suffixSame
    cases suffixSame

end MicroCFTA.SourcePruningEnumerationOpaqueEvent
