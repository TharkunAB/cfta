theorem prepareChild_complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationState.State Symbol EnumGuard)
    (scs : List EnumerationState.Suspended) (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : InternedProbeProvenance.Available heap value) (closed : value.free = [])
    (realized : PendingRealized heap before) (aligned : before.counter = before.values.length)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    ∃ node : Nat, encodeNode value = some node ∧ lookupNode heap node = some value ∧
      (value = .empty →
        prepareChild scs value = some (reject : EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol)) ∧
        ¬ ∃ (fragment : Fragments.Fragment Symbol) (after : EnumerationState.State Symbol EnumGuard),
          Success (reject : EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol)) before fragment after) ∧
      (value ≠ .empty →
