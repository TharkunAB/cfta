    subst action
    exact (EnumerationSchedule.reject_unsuccessful before after fragment observed).elim
  | reference _name =>
    simp [SourcePruningEnumerationShallowChild.prepareChild] at prepared
  | node entry _edges _depth _free =>
    by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
    · simp [SourcePruningEnumerationShallowChild.prepareChild, terminal] at prepared
    simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, Bool.false_eq_true,
      ↓reduceIte, SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
    subst action
    have nodeShape : fragment = .hole before.counter ∧
      after = {allocated (some (entry.identity + 1)) before with
        values := (allocated (some (entry.identity + 1)) before).values.set before.counter
          (.unenumerated (some (entry.identity + 1)) scs)} := by
      unfold Success at observed
      rw [bind_single _ _ before (allocated (some (entry.identity + 1)) before)
        before.counter (allocate_exact _ _)] at observed
      simpa [setValue, bind, pure, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.bind, StateT.pure, StateT.modifyGet, ExceptT.bind, ExceptT.pure,
        ExceptT.bindCont, ExceptT.mk, ExceptT.run, eq_comm] using observed
    obtain ⟨rfl, rfl⟩ := nodeShape
    refine ⟨set_storage _ (allocation_storage _ before storage) before.counter
      (.unenumerated (some (entry.identity + 1)) scs) ?_, Nat.lt_succ_self _, Nat.le_succ _⟩
    exact fun sc member => Nat.lt_trans (bounded sc member) (Nat.lt_succ_self _)
  | union entry _members _depth _free =>
    by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
    · simp [SourcePruningEnumerationShallowChild.prepareChild, terminal] at prepared
    simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, Bool.false_eq_true,
      ↓reduceIte, SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
    subst action
    have unionShape : fragment = .hole before.counter ∧
      after = allocated (some (entry.identity + 1)) before := by
      unfold Success at observed
      rw [bind_single _ _ before (allocated (some (entry.identity + 1)) before)
        before.counter (allocate_exact _ _)] at observed
      simpa [pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run, eq_comm] using observed
    obtain ⟨rfl, rfl⟩ := unionShape
    exact ⟨allocation_storage _ before storage, Nat.lt_succ_self _, Nat.le_succ _⟩
  | mu entry _body _depthShape _ordinaryShape =>
    by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
    · simp [SourcePruningEnumerationShallowChild.prepareChild, terminal] at prepared
    simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, Bool.false_eq_true,
      ↓reduceIte, SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
    subst action
    have muShape : fragment = .hole before.counter ∧
      after = allocated (some (entry.identity + 1)) before := by
      unfold Success at observed
      rw [bind_single _ _ before (allocated (some (entry.identity + 1)) before)
        before.counter (allocate_exact _ _)] at observed
      simpa [pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run, eq_comm] using observed
    obtain ⟨rfl, rfl⟩ := muShape
    exact ⟨allocation_storage _ before storage, Nat.lt_succ_self _, Nat.le_succ _⟩

/-- The actual captured child list preserves storage through its completed prefix. -/
