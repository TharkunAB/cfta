import MicroCFTA.SourcePruningEnumerationObservation

/-!
# Encoded writes of complete available node values

Actual allocation and raw replacement derive their handles and stored payloads.
Old pending slots retain their complete closed available values. Native index
cache correspondence, narrowing and intersection producers remain separate.
-/
namespace MicroCFTA.SourcePruningEnumerationWrites
open EnumerationState EnumerationCorrectness
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

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

/-- Replace one allocated raw slot with a derived complete available value. -/
theorem write_available_realized
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationState.State Symbol EnumGuard)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard) (slot : Nat)
    (scs : List EnumerationState.Suspended)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : InternedProbeProvenance.Available heap value) (closed : value.free = [])
    (realized : PendingRealized heap before) (inside : slot < before.values.length) :
    ∃ (node : Nat) (after : EnumerationState.State Symbol EnumGuard),
      encodeNode value = some node ∧
      Success (setValue slot (.unenumerated (some node) scs)) before () after ∧
      after = {before with values := before.values.set slot (.unenumerated (some node) scs)} ∧
      after.values[slot]? = some (.unenumerated (some node) scs) ∧ PendingRealized heap after := by
  obtain ⟨node, encoded, decoded⟩ := available_readback heap value coherent available closed
  refine ⟨node, {before with values := before.values.set slot (.unenumerated (some node) scs)},
    encoded, ?_, rfl, List.getElem?_set_self inside, ?_⟩
  · exact (EnumerationDriver.modify_success _ _ _).mpr rfl
  · intro storedSlot storedNode storedScs stored
    change (before.values.set slot (.unenumerated (some node) scs))[storedSlot]? =
      some (.unenumerated (some storedNode) storedScs) at stored
    obtain old | fresh := List.mem_or_eq_of_mem_set (List.mem_of_getElem? stored)
    · obtain ⟨oldSlot, oldStored⟩ := List.getElem?_of_mem old
      exact realized oldSlot storedNode storedScs oldStored
    · simp only [UVarValue.unenumerated.injEq, Option.some.injEq] at fresh
      obtain ⟨rfl, rfl⟩ := fresh
      exact ⟨value, decoded, available, closed⟩

end MicroCFTA.SourcePruningEnumerationWrites
