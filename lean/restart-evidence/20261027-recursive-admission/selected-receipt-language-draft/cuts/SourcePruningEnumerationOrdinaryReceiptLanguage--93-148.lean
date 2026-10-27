theorem CompletedHeadReceipt.sound_ordinary_callback_input
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos} {metadata : Metadata Typing} {before : Cached}
    {checkEmpty : Bool} {uv : Nat} {scs : List Suspended} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)}
    {saved : SourceEndpointMemo.Memos} {after : Cached} {returnedInventory : Inventory} {returnedMemos : Memos}
    {scanInventory : Inventory} {scanCaller : Caller (bits + 2)} {scanMemos : Memos}
    {ordinaryBefore : Cached} {entryFuel entryTarget entryHandle : Nat}
    {entryValue : InternedConstructorTemplates.Value Symbol Constraint}
    (originalPacket : SourcePruningEnumerationRecursive.Packet formulas solver scanInventory
      scanCaller scanMemos metadata ordinaryBefore)
    (entry : Success
      (SourcePruningEnumerationEntry.enter scanCaller.checked.native.machine.heap entryFuel entryTarget)
      ordinaryBefore.core (uv, entryHandle, scs, entryValue) before.core)
    (scanPacket : SourcePruningEnumerationRecursive.Packet formulas solver scanInventory
      scanCaller scanMemos metadata before)
    (prefixPost : SourceCurrentAllocatedPartialInvariant.Post formulas solver inventory
      scanCaller caller memos)
    (receipt : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv scs edge bound fragment reached saved after returnedInventory returnedMemos)
    {graph : Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
    {callbackFuel : Nat} {recorded : Metadata Typing}
    {callbackAfter : EnumerationState.State Symbol Constraint}
    (recording : Success
      (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv (.inl fragment))
      after.core (false, recorded) callbackAfter)
    (canonical : Canonical ordinaryBefore.core)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (freshArity : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      arityAllows edge.children.length (EnumerationCorrectness.suspendedVars before.core.counter tries) = true)
    (retained : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ incoming bucket,
        (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
        (match incoming with | .node _ _ _ _ => True | _ => False) ∨
          bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = []) :
    ∃ (handle : Nat) (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (storedEdges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference),
      before.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
      lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free) ∧
      edge ∈ storedEdges ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
        Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient reached.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment callbackAfter →
        Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient scanCaller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment ordinaryBefore.core ∧
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient edge (assignment uv) ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient (.node parentEntry storedEdges depth free) (assignment uv) ∧
        (∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc) ∧
        Fragments.fill assignment fragment = assignment uv := by
