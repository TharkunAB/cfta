theorem recursive_preparation {EnumGuard NativeGuard : Type}
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationState.State Symbol EnumGuard) (scs : List Suspended)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (boundary : match value with | .mu _ _ _ _ | .union _ _ _ _ => True | _ => False)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : InternedProbeProvenance.Available heap value) (closed : value.free = [])
    (realized : PendingRealized heap before) (aligned : before.counter = before.values.length)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (canonical : Canonical before) :
    ∃ (handle : Nat) (action : EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol))
      (after : EnumerationState.State Symbol EnumGuard),
      encodeNode value = some handle ∧ lookupNode heap handle = some value ∧
      SourcePruningEnumerationShallowChild.prepareChild scs value = some action ∧
      Success action before (.hole before.counter) after ∧
      after = allocated (some handle) before ∧
      after.values[before.counter]? = some (.unenumerated (some handle) []) ∧ Canonical after := by
