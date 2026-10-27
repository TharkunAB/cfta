
/-- A completed selected edge and its actual finalizer retain every other incoming-free root. -/
theorem completed_incoming_preserved
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before : Cached)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (checkEmpty : Bool) (target handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (selected : edge ∈ edges) (pending : EnumerationDependencies.InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (ranges : SourcePruningEnumerationSelectedEdge.Ranges checkEmpty scs edge caller before memos.query)
    (held : Nat) (inside : held < before.core.counter) (root : IsRoot before.core.representatives held)
    (incoming : IncomingAvoid held before.core) (different : held ≠ target)
    {r n p h k : Nat} {fragment : Fragments.Fragment Symbol}
    {reached : Caller width} {saved : Queries} {middle after : Cached} {finishFuel : Nat}
    (observed : ∀ er en P H ek, p ≤ P → h ≤ H →
      SourcePruningEnumerationSelectedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
        scs edge caller before memos.query = .complete fragment reached saved middle)
    (finalized : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
      finishFuel target fragment middle = some after) :
    EnumerationDriver.Protected held before.core after.core ∧ IncomingAvoid held after.core := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨value, lookup, available, closed⟩ := realized target handle scs stored
  have valueSame : value = .node parentEntry edges depth free :=
    Option.some.inj (lookup.symm.trans decoded)
  subst value
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    packet.safe.1.values _ (List.mem_of_getElem? stored)
  have avoids : Avoids before.core.representatives held scs :=
    incoming _ (List.mem_of_getElem? stored)
  obtain ⟨R, N, P, H, K, selectedCaller, selectedAfter, selectedQueries, final, next, afterRoots,
    result, running, _post, _query, _growth, _paths, _storage, _realized, _counts, _flags,
    _origin, _retained, protects, _pending, incomingHistory, shape⟩ :=
    SourcePruningEnumerationSelectedEdge.complete_with_fragments formulas solver inventory caller before checkEmpty
      parentEntry edges depth free edge scs roots memos packet.context available closed selected packet.safe realized
      paths counts flags bounded pending allowed tries residual projected ranges
  have actual := observed R N (max p P) (max h H) K (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  rw [Nat.add_comm r R, Nat.add_comm n N, Nat.add_comm k K] at actual
  have resultSame : result = .complete fragment reached saved middle :=
    (running r n (max p P) (max h H) k (Nat.le_max_right _ _) (Nat.le_max_right _ _)).symm.trans actual
  rcases shape with ⟨chosenFragment, completed, _safe, _bound, _pendingFragment, _separate⟩ |
    ⟨fragments, outer, waiting, stopped⟩
  · have middleSame : selectedAfter = middle :=
      (SourcePruningEnumerationSelectedEdge.Result.complete.inj (completed.symm.trans resultSame)).2.2.2
    have protectedMiddle : EnumerationDriver.Protected held before.core middle.core := by
      rw [← middleSame]
      exact protects held inside root avoids
    have incomingMiddle : IncomingAvoid held middle.core := by
      rw [← middleSame]
      exact incomingHistory held inside root avoids incoming
    have core := finalized_core reached.checked.native.machine.heap finishFuel target fragment middle after finalized
    have protectedFinal : EnumerationDriver.Protected held middle.core after.core := by
      refine ⟨?_, ?_, ?_⟩
      · rw [core]
        exact List.getElem?_set_ne (Ne.symm different)
      · rw [core]
        exact protectedMiddle.root
      · rw [core]
        exact fun _ => Iff.rfl
    refine ⟨protectedMiddle.trans protectedFinal, ?_⟩
    intro value member sc listed same
    rw [core] at member same
    rcases List.mem_or_eq_of_mem_set member with old | replaced
    · exact incomingMiddle value old sc listed same
    · subst value
      simp [references] at listed
  · rw [stopped] at resultSame
    cases resultSame

end MicroCFTA.SourcePruningEnumerationCapturedEdge
