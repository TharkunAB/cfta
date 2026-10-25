/-- Pure equality allocations retain every complete realized pending node value. -/
theorem suspended_realized (count : Nat)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (before : EnumerationState.State Symbol Constraint) (realized : PendingRealized heap before) :
    PendingRealized heap (suspendedState count before)
 := by
  induction count generalizing before with
  | zero => exact realized
  | succ count ih =>
      apply ih (allocated none before)
      intro slot node scs stored
      change (before.values ++ [.unenumerated none []])[slot]? =
        some (.unenumerated (some node) scs) at stored
      obtain old | fresh := List.mem_append.mp (List.mem_of_getElem? stored)
      · obtain ⟨oldSlot, oldStored⟩ := List.getElem?_of_mem old
        exact realized oldSlot node scs oldStored
      · simp at fresh

