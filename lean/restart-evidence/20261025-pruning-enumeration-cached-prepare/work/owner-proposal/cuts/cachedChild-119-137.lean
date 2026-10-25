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
