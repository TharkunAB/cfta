      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (ranges : Ranges checkEmpty uv scs before selectedEdges caller memos.query)
    (canonical : Canonical before.core) :
    ∃ (r n p h k : Nat) (processed : List (Receipt width)) (afterCaller : Caller width) (saved : Queries)
      (final : Memos) (next : Inventory) (result : Result width),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationNativeBranches.run checkEmpty (r + er) (n + en) P H (k + ek)
          uv scs before selectedEdges caller memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = saved ∧
      (∀ receipt ∈ processed, Admitted uv receipt) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        ∀ receipt ∈ processed, Pending receipt) ∧
      (∀ receipt ∈ processed,
        ∃ (reached : Caller width) (savedQueries : Queries) (receiptInventory : Inventory) (receiptMemos : Memos),
          advance receipt = some (reached, savedQueries) ∧
          Post formulas solver receiptInventory caller reached receiptMemos ∧ receiptMemos.query = savedQueries) ∧
      (∀ receipt ∈ processed, FragmentHistory before.core receipt) ∧
      (result = .complete processed afterCaller saved ∨ result = .stopped processed (some .unhandled)) ∧
      ((∀ edge ∈ selectedEdges, arityAllows edge.children.length scs = true →
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) →
        result = .complete processed afterCaller saved) ∧
      (∀ (fragment : Fragment) (reached : Caller width) (queries : Queries) (after : Cached),
        .complete fragment reached queries after ∈ processed → Canonical after.core) := by
  obtain ⟨r, n, p, h, k, processed, afterCaller, saved, final, next, result,
    stable, post, querySame, admitted, pendingHistory, receiptPosts, fragmentHistory, shape, supported⟩ :=
    complete_with_history formulas solver inventory caller before checkEmpty uv handle scs parentEntry
      storedEdges selectedEdges depth free roots memos initial ready stored decoded realized selected paths counts
      flags pending ranges
  have receiptView : processedReceipts result = processed := by
    rcases shape with completed | stopped
    · rw [completed]
      rfl
    · rw [stopped]
      rfl
  have actual : SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k uv scs before
      selectedEdges caller memos.query = result := by
    simpa only [Nat.add_zero] using stable 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  have canonicalResults := observed_canonical formulas solver inventory caller before checkEmpty uv handle scs
    parentEntry storedEdges selectedEdges depth free roots memos initial ready stored decoded realized selected
    paths counts flags pending canonical actual (by simpa only [receiptView] using receiptPosts)
  refine ⟨r, n, p, h, k, processed, afterCaller, saved, final, next, result,
    stable, post, querySame, admitted, pendingHistory, receiptPosts, fragmentHistory, shape, supported, ?_⟩
  simpa only [receiptView] using canonicalResults

end MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
