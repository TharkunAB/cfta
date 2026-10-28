/-- Every actual attached child cache retains its input carriers and references. -/
theorem candidate_carriers
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (safe : Safe before.core) (references : ReferencesCarry before.core) (after : Cached)
    (candidate : (run checkEmpty r n p h k scs incoming caller before queries).2 = some after) :
    UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
      ReferencesCarry after.core := by
  by_cases empty : incoming = .empty
  · have same : before = after := by simpa only [run, empty, ↓reduceIte, Option.some.injEq] using candidate
    subst after
    exact ⟨safe.1.total, .refl _, references⟩
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
          apply SourcePruningEnumerationCachedPrepare.cache_carriers
            caller.checked.native.machine.heap k scs incoming before after safe references
          simp only [run, ite_eq_right empty, partitioned] at candidate
          cases prepared : SourcePruningEnumerationCachedPrepare.prepareChild
              caller.checked.native.machine.heap k scs incoming before with
          | none => simpa only [prepared] using candidate
          | some rows =>
              cases rows with
              | nil => simpa only [prepared] using candidate
              | cons row tail =>
                  rcases row with ⟨fragment, reached⟩
                  cases tail with
                  | nil => simpa only [prepared] using candidate
                  | cons next rest => simpa only [prepared] using candidate
      | cons first rest =>
          apply SourcePruningEnumerationCachedTerminalAdapter.candidate_carriers
            checkEmpty r n p h k first rest caller before incoming descendants queries
            safe.1.total references after
          simpa only [run, empty, ↓reduceIte, partitioned] using candidate

/-- Every successful child singleton supplies graph carriers for its exact returned fragment. -/
theorem successful_carriers
    {checkEmpty : Bool} {r n p h k : Nat} {scs : List Suspended} {incoming : Node}
    {caller reachedCaller : Caller width} {before after : Cached} {queries savedQueries : Queries}
    {fragment : Fragment} {returned outer : Core} {waiting : EnumerationWaitingIndex.Waiting}
    (safe : Safe before.core) (references : ReferencesCarry before.core)
    (observed : run checkEmpty r n p h k scs incoming caller before queries =
      ((.ok (some [.ok (fragment, returned)]), reachedCaller, savedQueries, outer, waiting), some after)) :
    UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
      ReferencesCarry after.core ∧ FragmentCarries after.core fragment := by
  have candidateFacts := candidate_carriers checkEmpty r n p h k scs incoming caller before queries
    safe references after (by rw [observed])
  refine ⟨candidateFacts.1, candidateFacts.2.1, candidateFacts.2.2, ?_⟩
  have coreSame := singleton_core checkEmpty r n p h k scs incoming caller reachedCaller before after
    queries savedQueries fragment returned outer waiting observed
  rw [coreSame]
  have original := (erase checkEmpty r n p h k scs incoming caller before queries).symm.trans
    (congrArg Prod.fst observed)
  by_cases empty : incoming = .empty
  · simp only [observe, empty, ↓reduceIte] at original
    cases original
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
          simp only [observe, empty, ↓reduceIte, partitioned] at original
          cases prepared : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) scs incoming with
          | none => simp only [prepared] at original; cases original
          | some action =>
              rw [prepared] at original
              have rawSame := congrArg Prod.fst original
              dsimp only at rawSame
              have success : Success action before.core fragment returned := by
                rw [Success, Option.some.inj (Except.ok.inj rawSame)]
                exact List.mem_singleton_self _
              exact (SourcePruningEnumerationShallowChild.prepared_carriers scs incoming before.core
                returned action fragment safe references prepared success).2.2
      | cons first rest =>
          apply (SourcePruningEnumerationTerminal.successful_carriers checkEmpty r n p h first rest
            before.waiting caller before.core incoming descendants queries fragment reachedCaller
            savedQueries outer returned waiting safe.1.total references ?_).2.2.2
          simpa only [observe, empty, ↓reduceIte, partitioned] using original
