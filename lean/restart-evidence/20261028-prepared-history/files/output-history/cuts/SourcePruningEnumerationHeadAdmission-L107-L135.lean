    (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
    (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k uv scs edge caller before queries =
      some (.complete fragment reached saved after)) :
    arityAllows edge.children.length scs = true ∧
      ∃ (tries : List EqualityTrie.Trie) (residual : Option Constraint),
        SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · refine ⟨allowed, ?_⟩
    cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        rw [SourcePruningEnumerationCapturedEdge.run,
          SourcePruningEnumerationSelectedEdge.unsupported checkEmpty r n p h k scs edge caller before queries
            allowed projected] at observed
        cases observed
    | some pair =>
        obtain ⟨tries, residual⟩ := pair
        exact ⟨tries, residual, rfl⟩
  · have rejected : arityAllows edge.children.length scs = false := by
      cases actual : arityAllows edge.children.length scs with
      | false => rfl
      | true => exact (allowed actual).elim
    rw [SourcePruningEnumerationCapturedEdge.run,
      SourcePruningEnumerationSelectedEdge.arity_rejected checkEmpty r n p h k scs edge caller before queries
        rejected] at observed
    cases observed

/-- Keep the full finite producer packet and expose the actual completed head's admission. -/
theorem head_finite_complete_resources_with_receipt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
