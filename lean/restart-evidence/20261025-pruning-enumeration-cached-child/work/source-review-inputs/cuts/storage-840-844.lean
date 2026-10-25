/-- Actual allocation preserves finite storage bounds and the absence of old references to the new variable. -/
theorem allocation_storage (node : Option Nat) (state : State Symbol Guard) (valid : StorageValid state) :
    StorageValid (allocated node state) := by
  refine ⟨allocated_supply node state valid.aligned, valid.total,
    forestBound_mono state.counter (state.counter + 1) (by omega) state.representatives valid.forest, ?_, ?_⟩
