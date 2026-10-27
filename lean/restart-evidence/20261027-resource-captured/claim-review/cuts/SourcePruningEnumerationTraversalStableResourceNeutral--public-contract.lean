theorem stable_complete_neutral_semantics_resources
    (seed : SourcePruningEnumerationIncomingReservation.Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (inputs : List (Node × List Suspended))
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (genuine : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      Available beforeCaller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
      (∀ sc ∈ bucket, sc.var < before.core.counter) ∧ InputsPending before.core bucket)
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits seed.2 beforeCaller.checked)
    (reserved : SourcePruningEnumerationIncomingReservation.Reserved bits seed (cost inputs))
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      beforeCaller.checked.native.machine.heap)
    {r n p h k : Nat} {fragments : List Fragment} {afterCaller : Caller (bits + 2)}
    {after : Cached} {savedQueries : Queries}
    (observed : ∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
      SourcePruningEnumerationChildTraversal.run checkEmpty (r + extraRepresentative) (n + extraNative)
        P H (k + extraIndex) inputs beforeCaller before memos.query =
        .complete fragments afterCaller savedQueries after) :
    ∀ (held : Nat), held < before.core.counter → IsRoot before.core.representatives held →
    (∀ incoming bucket, (incoming, bucket) ∈ inputs → Avoids before.core.representatives held bucket) →
    ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (residualMeaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol),
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held after.core) ↔
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held before.core) ∧
      All₂ (fun input fragment =>
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient input.1 (Fragments.fill assignment fragment) ∧
        ∀ sc ∈ (match input.1 with
          | .node _ _ _ _ => input.2
          | _ => if input.2.any (fun sc => EqualityTrie.isTerminal sc.trie) then input.2 else []),
          Suspended.Holds assignment (Fragments.fill assignment fragment) sc) inputs fragments := by
