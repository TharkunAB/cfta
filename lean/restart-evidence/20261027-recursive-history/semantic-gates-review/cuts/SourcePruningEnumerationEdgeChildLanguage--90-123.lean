theorem restrictions_from_children
    (holds : Constraint → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment : Nat → Term Symbol) (edge : EdgeValue Symbol Constraint)
    (scs : List Suspended) (start : Nat) (tries : List EqualityTrie.Trie)
    (fragments : List Fragment)
    (forest : InternedGuardedLanguage.forest holds ambient edge.children
      (fragments.map (Fragments.fill assignment)))
    (descendants : ∀ index child, (fragments.map (Fragments.fill assignment))[index]? = some child →
      ∀ sc ∈ descendScs index (scs ++ suspendedVars start tries), Suspended.Holds assignment child sc)
    (valid : ∀ trie ∈ tries, EqualityTrie.Valid trie)
    (freshArity : arityAllows edge.children.length (suspendedVars start tries) = true)
    (inheritedValid : EnumerationSemantics.ValidSuspended scs)
    (originalArity : arityAllows edge.children.length scs = true)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    (∀ trie ∈ tries,
      EqualityHolds (.node edge.entry.key.symbol (fragments.map (Fragments.fill assignment))) trie) ∧
      ∀ sc ∈ scs, Suspended.Holds assignment
        (.node edge.entry.key.symbol (fragments.map (Fragments.fill assignment))) sc := by
  have lengthSame : (fragments.map (Fragments.fill assignment)).length = edge.children.length :=
    ((InternedGuardedLanguage.forest_all holds ambient edge.children _).mp forest).length_eq.symm
  constructor
  · apply edge_equalities_from_children assignment edge.entry.key.symbol
      (fragments.map (Fragments.fill assignment)) tries start scs valid
      (by simpa only [lengthSame] using freshArity) descendants
  · apply suspended_descent_complete assignment edge.entry.key.symbol
      (fragments.map (Fragments.fill assignment)) scs inheritedValid
      (by simpa only [lengthSame] using originalArity)
    · intro sc member terminal
      exact False.elim ((List.any_eq_false.mp nonterminal sc member) terminal)
    · intro index child found sc member
      exact descendants index child found sc (descendScs_mono index scs
        (scs ++ suspendedVars start tries) (fun _ present => List.mem_append_left _ present) member)

end MicroCFTA.SourcePruningEnumerationEdgeChildLanguage
