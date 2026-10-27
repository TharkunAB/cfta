/-- Original head resources preserve every different isolated root at the actual completed cache. -/
theorem CompletedHeadReceipt.isolated
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos} {metadata : Metadata Typing} {before : Cached}
    {checkEmpty : Bool} {uv : Nat} {scs : List Suspended} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)}
    {saved : Queries} {after : Cached} {returnedInventory : Inventory} {returnedMemos : Memos}
    (receipt : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv scs edge bound fragment reached saved after returnedInventory returnedMemos)
    {held heldHandle : Nat} (isolated : IsolatedPending held heldHandle before.core)
    (different : held ≠ uv) : IsolatedPending held heldHandle after.core := by
  obtain ⟨handle, parentEntry, storedEdges, depth, free, stored, decoded, selected⟩ := receipt.admission.source
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := receipt.admission.packet.valid
  obtain ⟨tries, residual, projected⟩ := receipt.projected
  have reserved : SourcePruningEnumerationIncomingReservation.Reserved bits seed
      (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries) := by
    simpa only [SourcePruningEnumerationNativeBranchCompletion.edgeCost, receipt.allowed,
      projected, ↓reduceIte] using receipt.admission.reserved
  have pending := EnumerationReferences.pending_inputs before.core receipt.admission.packet.pending
    uv (some handle) scs stored
  obtain ⟨value, lookup, available, closed⟩ := realized uv handle scs stored
  have sameValue : value = .node parentEntry storedEdges depth free :=
    Option.some.inj (lookup.symm.trans decoded)
  subst value
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    receipt.admission.packet.safe.1.values _ (List.mem_of_getElem? stored)
  have inside : held < before.core.counter := by
    rw [receipt.admission.packet.safe.1.aligned]
    exact (List.getElem?_eq_some_iff.mp isolated.stored).1
  have avoids : Avoids before.core.representatives held scs :=
    isolated.incoming _ (List.mem_of_getElem? stored)
  obtain ⟨r, n, p, h, k, selectedCaller, middle, selectedQueries, final, next, afterRoots,
    result, running, _post, _querySame, _growth, _paths, _storage, _realized, _counts, _flags,
    _origin, _retained, protects, _pendingHistory, incomingHistory, shape, _returnedFits, _returnedKnown⟩ :=
    SourcePruningEnumerationSelectedEdge.complete_with_fragments_resources seed formulas solver inventory caller before checkEmpty
      parentEntry storedEdges depth free edge scs roots memos receipt.admission.packet.context available closed selected
      receipt.admission.packet.safe realized paths counts flags bounded pending receipt.allowed tries residual projected
      receipt.admission.bounded reserved receipt.admission.known
  let w := bound + r + n + p + h + k
  have rl : r ≤ w := by dsimp [w]; omega
  have nl : n ≤ w := by dsimp [w]; omega
  have pl : p ≤ w := by dsimp [w]; omega
  have hl : h ≤ w := by dsimp [w]; omega
  have kl : k ≤ w := by dsimp [w]; omega
  have selectedAt : SourcePruningEnumerationSelectedEdge.run checkEmpty w w w w w scs edge
      caller before memos.query = result := by
    simpa only [Nat.add_sub_of_le rl, Nat.add_sub_of_le nl, Nat.add_sub_of_le kl] using
      running (w - r) (w - n) w w (w - k) pl hl
  have capturedAt : SourcePruningEnumerationCapturedEdge.run checkEmpty w w w w w uv scs edge
      caller before memos.query = some (.complete fragment reached saved after) := by
    simpa only [w, Nat.add_assoc] using receipt.running (r + n + p + h + k)
  rcases shape with ⟨produced, completed, _safe, _bound, _pendingFragment, _separate⟩ |
    ⟨fragments, outer, waiting, stopped⟩
  · rw [completed] at selectedAt
    rw [SourcePruningEnumerationCapturedEdge.run, selectedAt] at capturedAt
    cases finalized : SourcePruningEnumerationFinalize.run selectedCaller.checked.native.machine.heap
        w uv produced middle with
    | none =>
        simp only [finalized, Option.map_none] at capturedAt
        cases capturedAt
    | some finished =>
        simp only [finalized, Option.map_some, Option.some.injEq] at capturedAt
        have finishedSame : finished = after :=
          (SourcePruningEnumerationSelectedEdge.Result.complete.inj capturedAt).2.2.2
        rw [← finishedSame]
        have protectedMiddle := protects held inside isolated.root avoids
        have incomingMiddle := incomingHistory held inside isolated.root avoids isolated.incoming
        have core := finalized_core selectedCaller.checked.native.machine.heap w uv produced middle finished finalized
        refine ⟨?_, ?_, ?_⟩
        · rw [core]
          exact protectedMiddle.root
        · rw [core, List.getElem?_set_ne (Ne.symm different)]
          exact protectedMiddle.value.trans isolated.stored
        · intro value member sc listed same
          rw [core] at member same
          rcases List.mem_or_eq_of_mem_set member with old | replaced
          · exact incomingMiddle value old sc listed same
          · subst value
            simp [references] at listed
  · rw [stopped] at selectedAt
    rw [SourcePruningEnumerationCapturedEdge.run, selectedAt] at capturedAt
    cases capturedAt
