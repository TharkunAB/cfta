/-- A bounded slot write preserves all concrete storage bounds. -/
theorem set_storage (state : State Symbol Guard) (valid : StorageValid state) (uv : Nat)
    (value : UVarValue Symbol) (bounded : SlotBound state.counter value) :
    StorageValid {state with values := state.values.set uv value} := by
  refine ⟨by simpa [SupplyAligned] using valid.aligned, valid.total, valid.forest, ?_, valid.guards⟩
  intro stored member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact valid.values stored old
  · simpa [same] using bounded

