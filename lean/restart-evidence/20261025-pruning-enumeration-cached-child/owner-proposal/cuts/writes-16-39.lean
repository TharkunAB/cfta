/-- Derive the actual fresh slot and retain all realized pending payloads. -/
theorem allocate_available_realized
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationState.State Symbol EnumGuard)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : InternedProbeProvenance.Available heap value) (closed : value.free = [])
    (realized : PendingRealized heap before) (aligned : before.counter = before.values.length) :
    ∃ node : Nat, encodeNode value = some node ∧
      Success (allocate (some node)) before before.counter (allocated (some node) before) ∧
      (allocated (some node) before).values[before.counter]? = some (.unenumerated (some node) []) ∧
      PendingRealized heap (allocated (some node) before) := by
  obtain ⟨node, encoded, decoded⟩ := available_readback heap value coherent available closed
  refine ⟨node, encoded, ?_, allocated_slot (some node) before aligned, ?_⟩
  · simp only [Success, allocate_exact, ExceptT.run, List.mem_singleton]
  · intro storedSlot storedNode storedScs stored
    change (before.values ++ [.unenumerated (some node) []])[storedSlot]? =
      some (.unenumerated (some storedNode) storedScs) at stored
    obtain old | fresh := List.mem_append.mp (List.mem_of_getElem? stored)
    · obtain ⟨oldSlot, oldStored⟩ := List.getElem?_of_mem old
      exact realized oldSlot storedNode storedScs oldStored
    · simp only [List.mem_singleton, UVarValue.unenumerated.injEq, Option.some.injEq] at fresh
      obtain ⟨rfl, rfl⟩ := fresh
      exact ⟨value, decoded, available, closed⟩
