      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
        tries.length ≤ own) :
    ∃ (r n p h k : Nat) (receipt : Receipt (bits + 2)) (afterCaller : Caller (bits + 2)) (saved : Queries)
      (final : Memos) (next : Inventory),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationCapturedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
          uv scs edge caller before memos.query = some receipt) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = saved ∧ Admitted uv receipt ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        Pending receipt) ∧
      FragmentHistory before.core receipt ∧
      (advance receipt = some (afterCaller, saved) ∨
        receipt = .unhandled ∧ arityAllows edge.children.length scs = true ∧
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint = none) ∧
      Fits (reservationAdvance seed (edgeCost scs before.core.counter edge)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (reservationAdvance seed (edgeCost scs before.core.counter edge)).1)
        afterCaller.checked.native.machine.heap ∧
      HeadCacheBounds before scs arity own receipt ∧
      (∀ (flat : FlatCached), EnumerationFlatCached.Related flat before →
        ∀ en P H, p ≤ P → h ≤ H →
          ∃ flatReceipt,
            SourceFlatPruningCapturedEdge.run checkEmpty (n + en) P H uv scs edge
              caller flat memos.query = some flatReceipt ∧
            SourceFlatPruningSelectedEdge.ResultRelated flatReceipt receipt) := by
  obtain ⟨r, n, p, h, k, receipt, afterCaller, saved, final, next,
    running, post, queries, admitted, pendingHistory, history, shape, returnedFits, returnedKnown, flatRunning⟩ :=
    head_complete_resources seed formulas solver inventory caller before checkEmpty uv handle scs
      parentEntry edges depth free edge roots memos initial ready stored decoded realized selected
      paths counts flags pending fits reserved known
  refine ⟨r, n, p, h, k, receipt, afterCaller, saved, final, next,
    running, post, queries, admitted, pendingHistory, history, shape, returnedFits, returnedKnown, ?_, flatRunning⟩
  have observed := running 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at observed
  exact observed_head_cache_bounds checkEmpty r n p h k uv scs edge caller before memos.query
    arity own arityBound ownBound receipt observed


end MicroCFTA.SourceFlatPruningNativeHeadResources
