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
