theorem packet_boundary_prepare_created_isolated
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : Metadata Typing) (before after : Cached)
    (value : Value Symbol Constraint) (scs : List Suspended) (fuel : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (observed : SourcePruningEnumerationCachedPrepare.prepareChild caller.checked.native.machine.heap
      fuel scs value before = some [(.hole before.core.counter, after)]) :
    ∃ handle, encodeNode value = some handle ∧
      lookupNode caller.checked.native.machine.heap handle = some value ∧
      IsolatedPending before.core.counter handle after.core ∧ after.expandable before.core.counter = false := by
  obtain ⟨roots, paths, storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨handle, action, canonical, encoded, decoded, _prepared, running, _raw, shape, _stored,
    _growth, _aligned, _forest, _paths, _storage, _realized, _counts, _waiting, _sameFlags,
    returnedFlags, _holeBound⟩ := SourcePruningEnumerationCachedPrepare.boundary_complete
      caller.checked.native.machine.heap before value scs roots
      packet.context.ready.semantic.ready.semantic.1.normal.facts.coherent available closed boundary nonterminal
      storage realized paths counts flags
  have rowsSame := Option.some.inj ((running fuel).symm.trans observed)
  have afterSame : canonical = after := (Prod.mk.inj (List.cons.inj rowsSame).1).2
  rw [← afterSame]
  have isolated : IsolatedPending before.core.counter handle canonical.core := by
    rw [shape]
    exact allocated_isolated before.core handle packet.safe
  exact ⟨handle, encoded, decoded, isolated,
    isolated.disabled caller.checked.native.machine.heap canonical before.core.counter handle value
      decoded boundary returnedFlags⟩
