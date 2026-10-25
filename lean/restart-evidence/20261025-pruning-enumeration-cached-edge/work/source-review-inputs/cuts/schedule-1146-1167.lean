theorem descend_bounded (limit index : Nat) (scs : List Suspended) (bounded : ∀ sc ∈ scs, sc.var < limit) :
    ∀ sc ∈ descendScs index scs, sc.var < limit := by
  intro sc member
  simp only [descendScs, EqualityTrie.descendScs, List.mem_filter, List.mem_map] at member
  obtain ⟨⟨original, present, rfl⟩, _⟩ := member
  exact bounded original present

/-- The actual class-allocation traversal increases the supply by its list length. -/
theorem suspended_counter (count : Nat) (state : State Symbol Guard) :
    (suspendedState count state).counter = state.counter + count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => simpa [suspendedState, allocated, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (allocated none state)

/-- All consecutive suspended variables lie inside the extended allocation domain. -/
theorem suspended_bounded (start : Nat) (tries : List EqualityTrie.Trie) :
    ∀ sc ∈ suspendedVars start tries, sc.var < start + tries.length := by
  intro sc member
  have listed : sc.var ∈ (suspendedVars start tries).map EqualityTrie.Suspended.var := List.mem_map.mpr ⟨sc, member, rfl⟩
  rw [suspendedVars_variables] at listed
  obtain ⟨index, inside, same⟩ := List.mem_range'.mp listed
  omega
