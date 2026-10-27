/-- An actual prepared child preserves safety and every old allocated root. -/
theorem child
    (scs : List Suspended) (value : Node)
    (action : EnumerateM Symbol Constraint (Fragments.Fragment Symbol))
    (before after : EnumerationState.State Symbol Constraint)
    (fragment : Fragments.Fragment Symbol) (safe : Safe before)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild scs value = some action)
    (observed : Success action before fragment after) :
    Safe after ∧ EnumeratedOrigin before after ∧
    ∀ held, held < before.counter → IsRoot before.representatives held →
      EnumerationDriver.Protected held before after := by
  cases value with
  | empty =>
    simp only [SourcePruningEnumerationShallowChild.prepareChild, Option.some.injEq] at prepared
    subst action
    exact (reject_unsuccessful before after fragment observed).elim
  | reference _name =>
    simp [SourcePruningEnumerationShallowChild.prepareChild] at prepared
  | node entry _edges _depth _free =>
    by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
    · simp [SourcePruningEnumerationShallowChild.prepareChild, terminal] at prepared
    simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, Bool.false_eq_true,
      ↓reduceIte, SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
    subst action
    have shape : fragment = .hole before.counter ∧
        after = {allocated (some (entry.identity + 1)) before with
          values := (allocated (some (entry.identity + 1)) before).values.set before.counter
            (.unenumerated (some (entry.identity + 1)) scs)} := by
      unfold Success at observed
      rw [bind_single _ _ before (allocated (some (entry.identity + 1)) before)
        before.counter (allocate_exact _ _)] at observed
      simpa [setValue, bind, pure, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.bind, StateT.pure, StateT.modifyGet, ExceptT.bind, ExceptT.pure,
        ExceptT.bindCont, ExceptT.mk, ExceptT.run, eq_comm] using observed
    obtain ⟨rfl, rfl⟩ := shape
    exact fresh_write_effects _ scs before safe bounded
  | union entry _ _ _ | mu entry _ _ _ =>
    by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
    · simp [SourcePruningEnumerationShallowChild.prepareChild, terminal] at prepared
    simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, Bool.false_eq_true,
      ↓reduceIte, SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
    subst action
    have shape : fragment = .hole before.counter ∧
        after = allocated (some (entry.identity + 1)) before := by
      unfold Success at observed
      rw [bind_single _ _ before (allocated (some (entry.identity + 1)) before)
        before.counter (allocate_exact _ _)] at observed
      simpa [pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run, eq_comm] using observed
    obtain ⟨rfl, rfl⟩ := shape
    exact allocated_effects _ before safe
