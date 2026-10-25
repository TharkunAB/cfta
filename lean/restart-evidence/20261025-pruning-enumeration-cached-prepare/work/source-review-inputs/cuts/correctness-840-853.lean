/-- Actual allocation preserves finite storage bounds and the absence of old references to the new variable. -/
theorem allocation_storage (node : Option Nat) (state : State Symbol Guard) (valid : StorageValid state) :
    StorageValid (allocated node state) := by
  refine ⟨allocated_supply node state valid.aligned, valid.total,
    forestBound_mono state.counter (state.counter + 1) (by omega) state.representatives valid.forest, ?_, ?_⟩
  · intro value member
    simp only [allocated, List.mem_append, List.mem_singleton] at member
    rcases member with old | fresh
    · exact slotBound_mono state.counter (state.counter + 1) (by omega) value (valid.values value old)
    · subst value
      simp [SlotBound]
  · intro obligation member
    exact fragmentBound_mono state.counter (state.counter + 1) (by omega) obligation.2 (valid.guards obligation member)

