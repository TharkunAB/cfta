theorem boundary_complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (scs : List EnumerationState.Suspended) (roots : Nat → Nat)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : InternedProbeProvenance.Available heap value) (closed : value.free = [])
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (storage : StorageValid before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ (handle : Nat) (action : EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol))
      (after : EnumerationExpandableIndex.Cached Symbol EnumGuard),
      encodeNode value = some handle ∧ lookupNode heap handle = some value ∧
      SourcePruningEnumerationShallowChild.prepareChild scs value = some action ∧
      (∀ (fuel : Nat), prepareChild heap fuel scs value before =
        some [(.hole before.core.counter, after)]) ∧
      ExceptT.run (action before.core) = [.ok (.hole before.core.counter, after.core)] ∧
      after.core = EnumerationState.allocated (some handle) before.core ∧
      after.core.values[before.core.counter]? = some (.unenumerated (some handle) []) ∧
      after.core.counter = before.core.counter + 1 ∧
      after.core.counter = after.core.values.length ∧
      after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
      StorageValid after.core ∧ PendingRealized heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      after.waiting = before.waiting ∧ after.expandable = before.expandable ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      FragmentBound («Symbol» := Symbol) after.core.counter (.hole before.core.counter) := by
  have nonempty : value ≠ .empty := by
    intro emptyValue
    subst value
    cases boundary
  obtain ⟨handle, encoded, decoded, _emptyCase, nonemptyCase⟩ :=
    SourcePruningEnumerationShallowChild.prepareChild_complete heap before.core scs value
      coherent available closed realized storage.aligned nonterminal
