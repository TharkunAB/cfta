theorem narrowed_receipt_sound
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller (bits + 2)) (before : Cached) (memos : Memos)
    (checked : Core)
    (prepared : MergedSourceComparison.Result Symbol Constraint
      (Node × Option (EnumerateM Symbol Constraint Unit)))
    (ordinaryCaller : Caller (bits + 2)) (ordinaryMemos : Memos) (narrowed : Cached)
    (action : Option (List (Except Error (Unit × Core))))
    (right : Option (List (Except Error ((Bool × Metadata Typing) × Core))))
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (canonical : Canonical before.core)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos
      (runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before memos.query))
    (actual : runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
      uv caller before memos.query =
        .narrowed checked prepared ordinaryCaller ordinaryMemos.query action (some narrowed) right none)
    (entryFuel target entryHandle : Nat) (scs : List Suspended) (entryValue : Node) (entered : Cached)
    (entry : Success
      (SourcePruningEnumerationEntry.enter ordinaryCaller.checked.native.machine.heap entryFuel uv)
      narrowed.core (target, entryHandle, scs, entryValue) entered.core)
    (enteredPacket : SourcePruningEnumerationRecursive.Packet formulas solver inventory
      ordinaryCaller ordinaryMemos metadata entered)
    (seed : Seed) (inherited : Nat)
    (headInventory : Inventory) (headCaller : Caller (bits + 2)) (headMemos : Memos)
    (edge : EdgeValue Symbol Constraint) (headBound : Nat)
    (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2))
    (saved : SourceEndpointMemo.Memos) (after : Cached)
    (returnedInventory : Inventory) (returnedMemos : Memos)
    (prefixPost : SourceCurrentAllocatedPartialInvariant.Post formulas solver headInventory
      ordinaryCaller headCaller headMemos)
    (receipt : SourcePruningEnumerationNativeHookResources.CompletedHeadReceipt seed inherited
      formulas solver headInventory headCaller headMemos metadata entered checkEmpty target scs edge headBound
      fragment reached saved after returnedInventory returnedMemos)
    (callbackFuel : Nat) (recorded : Metadata Typing) (callbackAfter : Core)
    (recording : Success
      (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata target (.inl fragment))
      after.core (false, recorded) callbackAfter)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (freshArity : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      arityAllows edge.children.length (EnumerationCorrectness.suspendedVars entered.core.counter tries) = true)
    (retained : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ incoming bucket,
        (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs entered.core.counter tries →
        (match incoming with | .node _ _ _ _ => True | _ => False) ∨
          bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = []) :
    ∃ (handle : Nat) (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (storedEdges : List (EdgeValue Symbol Constraint)) (depth : Nat)
      (free : List InternedBinderProtocol.Reference),
      narrowed.core.values[target]? = some (.unenumerated (some handle) scs) ∧
      lookupNode headCaller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free) ∧
      edge ∈ storedEdges ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
        Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient reached.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment callbackAfter →
        Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment before.core ∧
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient edge (assignment target) ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient (.node parentEntry storedEdges depth free) (assignment target) ∧
        (∀ sc ∈ scs, Suspended.Holds assignment (assignment target) sc) ∧
        Fragments.fill assignment fragment = assignment target := by
