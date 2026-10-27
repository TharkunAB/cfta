  | union entry members depth free | mu entry members depth free => rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual stable completed head retains its opaque child at the same final cache. -/
theorem completed_head_opaque_isolated
    (seed : Seed) (inherited : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before : Cached) (checkEmpty : Bool) (uv : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (bound : Nat) (fragment : Fragment)
    (reached : Caller (bits + 2)) (saved : Queries) (headCache : Cached)
    (returnedInventory : Inventory) (returnedMemos : Memos)
    (head : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv scs edge bound fragment reached saved headCache returnedInventory returnedMemos)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (consumed suffix : List (Node × List Suspended)) (value : Node) (bucket : List Suspended)
    (location : SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries =
      consumed ++ (value, bucket) :: suffix)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (nonterminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    ∃ held handle, lookupNode reached.checked.native.machine.heap handle = some value ∧
      EnumerationDischargeHistory.IsolatedPending held handle headCache.core := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := head.admission.packet.valid
  obtain ⟨handle, parentEntry, edges, depth, free, stored, decoded, selected⟩ := head.admission.source
  obtain ⟨parent, parentLookup, parentAvailable, parentClosed⟩ := realized uv handle scs stored
  have parentSame : parent = .node parentEntry edges depth free :=
    Option.some.inj (parentLookup.symm.trans decoded)
  subst parent
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    head.admission.ready.safe.1.values _ (List.mem_of_getElem? stored)
  have pending := EnumerationReferences.pending_inputs before.core head.admission.packet.pending
    uv (some handle) scs stored
  obtain ⟨_action, own, _prepared, ownRun, _raw, ownCore, ownCounter, _ownForest,
    ownSafe, ownPaths, ownRealized, ownCounts, ownFlags, _combinedPending, genuine, _ownProtects⟩ :=
    SourcePruningEnumerationEdgeInputs.complete caller.checked.native.machine.heap parentEntry edges depth free
      edge scs roots head.admission.packet.context.ready.semantic.ready parentAvailable parentClosed selected
      before head.admission.packet.safe realized paths counts flags bounded pending head.allowed tries residual projected
  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
  let staged := inputs.map (fun input => (input.1, input.2,
    SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1))
  have stagedInputs : staged.map (fun input => (input.1, input.2.1)) = inputs := by
    simp only [staged, List.map_map]
    exact List.map_id _
  have ownPacket := own_prefix_packet formulas solver inventory caller memos metadata before own tries.length
    head.admission.packet ownCore ⟨roots, ownPaths, ownSafe.1, ownRealized, ownCounts, ownFlags⟩
  have originalReserved : Reserved bits seed (cost inputs) := by
