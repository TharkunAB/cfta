theorem complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (InternedConstructorTemplates.EdgeValue Symbol NativeGuard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (scs : List EnumerationState.Suspended) (roots : Nat → Nat)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : InternedProbeProvenance.Available heap (.node entry edges depth free))
    (closed : free = [])
    (storage : StorageValid before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat),
      SourcePruningEnumerationNativeIndex.candidate heap
        ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    ∃ (handle : Nat) (action : EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol))
      (allocatedCached after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (fuel : Nat),
      encodeNode (.node entry edges depth free) = some handle ∧
      lookupNode heap handle = some (.node entry edges depth free) ∧
      SourcePruningEnumerationShallowChild.prepareChild scs (.node entry edges depth free) = some action ∧
      ExceptT.run (action before.core) = [.ok (.hole before.core.counter, after.core)] ∧
      allocate heap (some handle) before = some (before.core.counter, allocatedCached) ∧
      allocatedCached.core = EnumerationState.allocated (some handle) before.core ∧
      allocatedCached.core.values[before.core.counter]? = some (.unenumerated (some handle) []) ∧
      StorageValid allocatedCached.core ∧ PendingRealized heap allocatedCached.core ∧
      EnumerationCanonicalWaiting.Correct roots allocatedCached.core.values allocatedCached.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
        ((allocatedCached.core.values[slot]?).getD .eliminated) = some (allocatedCached.expandable slot)) ∧
      allocatedCached.waiting = before.waiting ∧
      (∀ (extra : Nat), writeSlot heap (fuel + extra) before.core.counter
        (.unenumerated (some handle) scs) allocatedCached = some after) ∧
      (∀ (extra : Nat), prepareOrdinary heap (fuel + extra) scs
        (.node entry edges depth free) before = some (.hole before.core.counter, after)) ∧
      after.core = {allocatedCached.core with values :=
                allocatedCached.core.values.set before.core.counter (.unenumerated (some handle) scs)} ∧
      after.core.values[before.core.counter]? = some (.unenumerated (some handle) scs) ∧
      after.core.counter = before.core.counter + 1 ∧ after.core.counter = after.core.values.length ∧
      after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
      StorageValid after.core ∧ PendingRealized heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      after.expandable =
        (fun slot => if slot = before.core.counter then true else before.expandable slot) ∧
      after.waiting = EnumerationCanonicalWaiting.count roots 1 scs before.waiting ∧
      FragmentBound («Symbol» := Symbol) after.core.counter (.hole before.core.counter) := by
