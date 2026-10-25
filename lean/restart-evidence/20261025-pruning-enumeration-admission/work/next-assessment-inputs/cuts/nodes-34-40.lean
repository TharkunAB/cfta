/-- A closed available value derives its exact handle and complete readback. -/
theorem available_readback (heap : State Symbol Guard) (value : Value Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : Available heap value) (closed : value.free = []) :
    ∃ node, encodeNode value = some node ∧ lookupNode heap node = some value := by
  cases value with
  | empty => exact ⟨0, rfl, rfl⟩
