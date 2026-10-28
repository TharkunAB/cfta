private theorem prepared_representatives
    (scs : List Suspended) (value : Value Symbol NativeGuard)
    (before after : EnumerationState.State Symbol EnumGuard)
    (action : EnumerateM Symbol EnumGuard (Fragment Symbol)) (fragment : Fragment Symbol)
    (prepared : prepareChild scs value = some action)
    (success : Success action before fragment after) :
    after.representatives = before.representatives := by
  cases value with
  | empty =>
      simp only [prepareChild, Option.some.injEq] at prepared
      rw [← prepared] at success
      exact (reject_unsuccessful before after fragment success).elim
  | reference name =>
      simp only [prepareChild, reduceCtorEq] at prepared
  | node entry edges depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [prepareChild, terminal, ↓reduceIte, reduceCtorEq] at prepared
      · simp only [prepareChild, terminal, Bool.false_eq_true, ↓reduceIte,
          SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, continued⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        have writtenSame := (EnumerationDriver.modify_success _
          (allocated (some (entry.identity + 1)) before) written).mp writing
        obtain ⟨_fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment written after).mp final
        subst after
        rw [writtenSame]
        rfl
  | union entry _ _ _ | mu entry _ _ _ =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [prepareChild, terminal, ↓reduceIte, reduceCtorEq] at prepared
      · simp only [prepareChild, terminal, Bool.false_eq_true, ↓reduceIte,
          SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨_fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment (allocated (some (entry.identity + 1)) before) after).mp final
        subst after
