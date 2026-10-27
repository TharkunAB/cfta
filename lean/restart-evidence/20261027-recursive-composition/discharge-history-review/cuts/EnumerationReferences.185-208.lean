theorem allocation_allowed (allowed : Nat → Prop) (node : Option Nat) (state : State Symbol Guard) (valid : ReferencesAllowed allowed state) :
    ReferencesAllowed allowed (allocated node state) := by
  intro value member
  rcases List.mem_append.mp member with old | fresh
  · exact valid value old
  · have same : value = .unenumerated node [] := by simpa using fresh
    simp [same, references, InputsAllowed]

/-- Repeated class allocation creates no stored references. -/
theorem suspension_allowed (allowed : Nat → Prop) (count : Nat) (state : State Symbol Guard) (valid : ReferencesAllowed allowed state) :
    ReferencesAllowed allowed (suspendedState count state) := by
  induction count generalizing state with
  | zero => exact valid
  | succ count ih => exact ih (allocated none state) (allocation_allowed allowed none state valid)

/-- Each returned fresh class variable is inside the future allocation region. -/
theorem suspended_allowed (allowed : Nat → Prop) (limit start : Nat) (tries : List EqualityTrie.Trie)
    (lower : limit ≤ start) (future : ∀ uv, limit ≤ uv → allowed uv) : InputsAllowed allowed (suspendedVars start tries) := by
  intro sc member
  have listed : sc.var ∈ (suspendedVars start tries).map EqualityTrie.Suspended.var := List.mem_map.mpr ⟨sc, member, rfl⟩
  rw [suspendedVars_variables] at listed
  obtain ⟨index, _, same⟩ := List.mem_range'.mp listed
  apply future sc.var
  omega
