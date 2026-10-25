theorem allocate_complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (node : Option Nat) (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (roots : Nat → Nat)
    (realizable : ∀ (handle : Nat), node = some handle →
      ∃ value : InternedConstructorTemplates.Value Symbol NativeGuard,
        lookupNode heap handle = some value ∧
        InternedProbeProvenance.Available heap value ∧ value.free = [])
    (storage : StorageValid before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ (flag : Bool) (after : EnumerationExpandableIndex.Cached Symbol EnumGuard),
      SourcePruningEnumerationNativeIndex.candidate heap (.unenumerated node []) = some flag ∧
      SourcePruningEnumerationCachedChild.allocate heap node before =
        some (before.core.counter, after) ∧
      ExceptT.run (EnumerationState.allocate node before.core) =
        [.ok (before.core.counter, after.core)] ∧
      after.core = EnumerationState.allocated node before.core ∧
      after.core.values[before.core.counter]? = some (.unenumerated node []) ∧
      after.core.counter = before.core.counter + 1 ∧
      after.core.counter = after.core.values.length ∧
      after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
      StorageValid after.core ∧ PendingRealized heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      after.waiting = before.waiting ∧
      after.expandable = (fun slot => if slot = before.core.counter then flag else before.expandable slot) ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) := by
