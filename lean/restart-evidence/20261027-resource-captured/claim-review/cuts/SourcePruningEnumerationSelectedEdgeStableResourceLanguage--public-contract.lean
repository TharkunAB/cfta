theorem stable_complete_semantics_resources
    (seed : SourcePruningEnumerationIncomingReservation.Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
    (parentClosed : free = []) (selected : edge ∈ edges)
    (safe : Safe before.core) (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits seed.2 caller.checked)
    (reserved : SourcePruningEnumerationIncomingReservation.Reserved bits seed
      (cost edge scs before.core.counter tries))
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      caller.checked.native.machine.heap)
    {r n p h k : Nat} {fragment : Fragment} {afterCaller : Caller (bits + 2)}
    {after : Cached} {savedQueries : Queries}
    (observed : ∀ er en P H ek, p ≤ P → h ≤ H →
      run checkEmpty (r + er) (n + en) P H (k + ek) scs edge caller before memos.query =
        .complete fragment afterCaller savedQueries after) :
    ∃ childFragments : List Fragment,
      fragment = .node edge.entry.key.symbol childFragments ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap) residualMeaning assignment after.core ↔
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap) residualMeaning assignment before.core ∧
        All₂ (fun (input : Node × List Suspended) (child : Fragment) =>
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient input.1 (Fragments.fill assignment child) ∧
          ∀ sc ∈ (match input.1 with
            | .node _ _ _ _ => input.2
            | _ => if input.2.any (fun sc => EqualityTrie.isTerminal sc.trie) then input.2 else []),
            Suspended.Holds assignment (Fragments.fill assignment child) sc)
          (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries) childFragments ∧
        ResidualHolds residualMeaning residual (Fragments.fill assignment fragment) := by
