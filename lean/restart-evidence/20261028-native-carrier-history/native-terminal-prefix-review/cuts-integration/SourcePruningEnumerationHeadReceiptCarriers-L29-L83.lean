/-- The original carrier invariant reaches this receipt's own cache and fragment. -/
theorem CompletedHeadReceipt.carriers
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos} {metadata : Metadata Typing} {before : Cached}
    {checkEmpty : Bool} {uv : Nat} {scs : List Suspended} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragment} {reached : Caller (bits + 2)} {saved : Queries} {after : Cached}
    {returnedInventory : Inventory} {returnedMemos : Memos}
    (receipt : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv scs edge bound fragment reached saved after returnedInventory returnedMemos)
    (references : ReferencesCarry before.core) :
    UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
      ReferencesCarry after.core ∧ FragmentCarries after.core fragment := by
  obtain ⟨handle, parentEntry, edges, depth, free, stored, decoded, selected⟩ := receipt.admission.source
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := receipt.admission.packet.valid
  obtain ⟨tries, residual, projected⟩ := receipt.projected
  have pending := EnumerationReferences.pending_inputs before.core receipt.admission.packet.pending
    uv (some handle) scs stored
  have actualReserved : Reserved bits seed
      (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries) := by
    simpa only [SourcePruningEnumerationNativeBranchCompletion.edgeCost, receipt.allowed,
      ↓reduceIte, projected] using receipt.admission.reserved
  obtain ⟨r, n, p, h, k, actualCaller, actualAfter, actualQueries, _actualMemos, _actualInventory,
    _actualRoots, result, running, _post, _query, _growth, _paths, storage, _realized, _counts,
    _flags, _origin, _pending, _protected, _pendingHistory, shape, _fits, _known, carried⟩ :=
    SourcePruningEnumerationCapturedEdge.complete_with_history_resources_carriers seed formulas solver inventory
      caller before checkEmpty uv handle scs parentEntry edges depth free edge roots memos
      receipt.admission.packet.context receipt.admission.ready stored decoded realized selected paths counts flags
      pending receipt.allowed tries residual projected receipt.admission.bounded actualReserved receipt.admission.known
  let common := bound + r + n + p + h + k
  have boundLe : bound ≤ common := by dsimp [common]; omega
  have rLe : r ≤ common := by dsimp [common]; omega
  have nLe : n ≤ common := by dsimp [common]; omega
  have pLe : p ≤ common := by dsimp [common]; omega
  have hLe : h ≤ common := by dsimp [common]; omega
  have kLe : k ≤ common := by dsimp [common]; omega
  have produced := running (common - r) (common - n) common common (common - k) pLe hLe
  rw [Nat.add_sub_of_le rLe, Nat.add_sub_of_le nLe, Nat.add_sub_of_le kLe] at produced
  have original := receipt.running (common - bound)
  rw [Nat.add_sub_of_le boundLe] at original
  have same : result = .complete fragment reached saved after :=
    Option.some.inj (produced.symm.trans original)
  obtain ⟨preserved, returnedReferences, fragmentCarried⟩ := carried references
  rcases shape with ⟨actualFragment, completed, _rest⟩ | ⟨_fragments, _outer, _waiting, stopped⟩
  · obtain ⟨fragmentSame, _callerSame, _queriesSame, afterSame⟩ :=
      SourcePruningEnumerationSelectedEdge.Result.complete.inj (same.symm.trans completed)
    have actualFragmentCarried : FragmentCarries actualAfter.core actualFragment := by
      simpa only [completed] using fragmentCarried
    rw [afterSame, fragmentSame]
    exact ⟨storage.total, preserved, returnedReferences, actualFragmentCarried⟩
  · rw [same] at stopped
    cases stopped

end MicroCFTA.SourcePruningEnumerationNativeHookResources
