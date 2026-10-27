    (ranges : SourcePruningEnumerationSelectedEdge.Ranges checkEmpty scs edge caller before memos.query)
    (canonical : Canonical before.core)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (freshArity : arityAllows edge.children.length (suspendedVars before.core.counter tries) = true)
    (retained : ∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
      (match incoming with | .node _ _ _ _ => True | _ => False) ∨
        bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = [])
    {bound : Nat} {fragment : Fragment} {afterCaller : Caller width}
    {after : Cached} {savedQueries : Queries}
    (observed : ∀ extra,
      run checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs edge caller before memos.query = some (.complete fragment afterCaller savedQueries after)) :
    ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment after.core →
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment before.core ∧
      InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient edge (assignment uv) ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient (.node parentEntry edges depth free) (assignment uv) ∧
      (∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc) ∧
      Fragments.fill assignment fragment = assignment uv := by
  obtain ⟨r, n, p, h, k, running⟩ :=
    stable_complete_of_diagonal formulas solver inventory caller before checkEmpty uv handle scs
      parentEntry edges depth free edge roots memos initial ready stored decoded realized selected
      paths counts flags pending allowed tries residual projected ranges observed
  exact stable_complete_sound_current formulas solver inventory caller before checkEmpty uv handle scs
    parentEntry edges depth free edge roots memos initial ready stored decoded realized selected
    paths counts flags pending allowed tries residual projected ranges canonical nonterminal freshArity retained running
