theorem opaque_suffix_complete_isolated_resources
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (original prepared : Cached) (value : Node) (bucket : List Suspended) (prepareFuel : Nat)
    (packet : Packet formulas solver inventory caller memos metadata original)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (nonterminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (observed : SourcePruningEnumerationCachedPrepare.prepareChild caller.checked.native.machine.heap
      prepareFuel bucket value original = some [(.hole original.core.counter, prepared)])
    (checkEmpty : Bool) (inputs : List (Node × List Suspended))
    (genuine : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      Available caller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
      (∀ sc ∈ bucket, sc.var < original.core.counter) ∧ InputsPending original.core bucket)
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (SourcePruningEnumerationTraversalCompletion.cost inputs))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (handle r n p h k : Nat) (fragments : List Fragment) (afterCaller : Caller (bits + 2))
      (after : Cached) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (afterRoots : Nat → Nat) (result : SourcePruningEnumerationChildTraversal.Result (bits + 2)),
      encodeNode value = some handle ∧ lookupNode caller.checked.native.machine.heap handle = some value ∧
      prepared.core = allocated (some handle) original.core ∧
      ((∀ er en P H ek, p ≤ P → h ≤ H →
          SourcePruningEnumerationChildTraversal.run checkEmpty (r + er) (n + en) P H (k + ek)
            inputs caller prepared memos.query = result) ∧
        Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
        prepared.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
        StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
        EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
        (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
          ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
        EnumeratedOrigin prepared.core after.core ∧
        (∀ held fragment, prepared.core.values[held]? = some (.enumerated fragment) →
          EnumerationDriver.Protected held prepared.core after.core) ∧
        (∀ held, held < prepared.core.counter → IsRoot prepared.core.representatives held →
          (∀ incoming bucket, (incoming, bucket) ∈ inputs → Avoids prepared.core.representatives held bucket) →
          EnumerationDriver.Protected held prepared.core after.core) ∧
        (∀ allowed, ReferencesAllowed allowed prepared.core →
          (∀ incoming bucket, (incoming, bucket) ∈ inputs → InputsAllowed allowed bucket) →
          ReferencesAllowed allowed after.core) ∧
        (PendingReferences prepared.core → PendingReferences after.core) ∧
        (∀ fragment ∈ fragments, FragmentBound after.core.counter fragment) ∧
        ((result = .complete fragments afterCaller savedQueries after ∧ Safe after.core ∧
            ∀ fragment ∈ fragments, PendingFragment after.core fragment ∧
              ∀ held, held < prepared.core.counter → IsRoot prepared.core.representatives held →
                (∀ incoming bucket, (incoming, bucket) ∈ inputs → Avoids prepared.core.representatives held bucket) →
                FragmentAvoid after.core.representatives held fragment) ∨
          ∃ outer waiting, result = .stopped fragments
            (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) ∧
        Fits (advance seed (SourcePruningEnumerationTraversalCompletion.cost inputs)).2 afterCaller.checked ∧
        Heap (fun guard => guard ∈ (advance seed (SourcePruningEnumerationTraversalCompletion.cost inputs)).1)
          afterCaller.checked.native.machine.heap) ∧
      IsolatedPending original.core.counter handle after.core ∧
      (∀ (residual : Option Constraint) (parentFragment : Fragment) (fuel target : Nat) (finished : Cached),
        target ≠ original.core.counter →
        SourcePruningEnumerationFinalize.run afterCaller.checked.native.machine.heap fuel target parentFragment
          (SourcePruningEnumerationSelectedEdge.finish residual parentFragment after) = some finished →
        IsolatedPending original.core.counter handle finished.core) := by
  obtain ⟨roots, paths, storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨handle, action, canonical, encoded, decoded, _action, running, _raw, core, _stored,
    _growth, _aligned, _forest, preparedPaths, _storage, preparedRealized, preparedCounts,
    _waiting, _sameFlags, preparedFlags, _holeBound⟩ :=
    SourcePruningEnumerationCachedPrepare.boundary_complete caller.checked.native.machine.heap original
      value bucket roots packet.context.ready.semantic.ready.semantic.1.normal.facts.coherent
      available closed boundary nonterminal storage realized paths counts flags
  have sameRows := Option.some.inj ((running prepareFuel).symm.trans observed)
  have sameCache : canonical = prepared := (Prod.mk.inj (List.cons.inj sameRows).1).2
  subst canonical
  have preparedSafe : Safe prepared.core := by
