theorem complete_sound_current_resources
    (seed : SourcePruningEnumerationIncomingReservation.Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : edge ∈ edges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits seed.2 caller.checked)
    (reserved : SourcePruningEnumerationIncomingReservation.Reserved bits seed
      (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries))
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (canonical : Canonical before.core)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (freshArity : arityAllows edge.children.length (suspendedVars before.core.counter tries) = true)
    (retained : ∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
      (match incoming with | .node _ _ _ _ => True | _ => False) ∨
        bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = []) :
    ∃ bound : Nat, ∀ (flat : FlatCached), EnumerationFlatCached.Related flat before →
      ∀ (extra : Nat) (fragment : Fragment) (reached : Caller (bits + 2))
        (saved : SourceEndpointMemo.Memos) (after : FlatCached),
      run checkEmpty (bound + extra) (bound + extra) (bound + extra)
        uv scs edge caller flat memos.query = some (.complete fragment reached saved after) →
      ∃ earlier : Cached,
        EnumerationFlatCached.Related after earlier ∧ Safe earlier.core ∧
        (∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
          ∃ nextLevel, EnumerationOrder.Stratified earlier.core nextLevel (frontier + 1)) ∧
        ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
          EnumerationFlatState.Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient reached.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            assignment after.core →
          EnumerationFlatState.Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            assignment flat.core ∧
          InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient edge (assignment uv) ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient (.node parentEntry edges depth free) (assignment uv) ∧
          (∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc) ∧
          Fragments.fill assignment fragment = assignment uv := by
