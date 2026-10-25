import MicroCFTA.SourcePruningEnumerationAssimilation

namespace MicroCFTA.SourcePruningEnumerationFinish
open EnumerationState EnumerationCorrectness
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourcePruningEnumerationAssimilation (finish)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {EnumGuard : Type}

/-- The existing finish action consumes the derived replacement without another query. -/
theorem finish_complete
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (before : EnumerationState.State Symbol EnumGuard)
    (result : InternedConstructorTemplates.Value Symbol Constraint)
    (source target sourceHandle targetHandle resultHandle : Nat)
    (sourceScs targetScs : List EnumerationState.Suspended)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : InternedProbeProvenance.Available heap result) (closed : result.free = [])
    (encoded : encodeNode result = some resultHandle)
    (realized : PendingRealized heap before)
    (sourceStored : before.values[source]? = some (.unenumerated (some sourceHandle) sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated (some targetHandle) targetScs))
    (different : target ≠ source) :
    (result = .empty →
      ExceptT.run (finish (EnumGuard := EnumGuard) source target resultHandle sourceScs targetScs result before) = []) ∧
    (result ≠ .empty → ∃ after : EnumerationState.State Symbol EnumGuard,
      ExceptT.run (finish (EnumGuard := EnumGuard) source target resultHandle sourceScs targetScs result before) =
        [.ok ((), after)] ∧
      after = assimilated before target source (.unenumerated (some resultHandle) (sourceScs ++ targetScs)) ∧
      after.values[target]? = some (.unenumerated (some resultHandle) (sourceScs ++ targetScs)) ∧
      after.values[source]? = some .eliminated ∧ PendingRealized heap after) := by
  constructor
  · intro isEmpty
    subst result
    rfl
  · intro nonempty
    have sourceInside : source < before.values.length := by
      exact (List.getElem?_eq_some_iff.mp sourceStored).elim (fun bound storedValue => bound)
    have targetInside : target < before.values.length := by
      exact (List.getElem?_eq_some_iff.mp targetStored).elim (fun bound storedValue => bound)
    obtain ⟨writtenHandle, middle, writtenEncoded, written, middleSame, middleStored, middleRealized⟩ :=
      SourcePruningEnumerationWrites.write_available_realized heap before result target
        (sourceScs ++ targetScs) coherent available closed realized targetInside
    have sameHandle : writtenHandle = resultHandle := by
      exact Option.some.inj (writtenEncoded.symm.trans encoded)
    subst writtenHandle
    subst middle
    have raw : ExceptT.run (finish (EnumGuard := EnumGuard) source target resultHandle sourceScs targetScs result before) =
        [.ok ((), assimilated before target source (.unenumerated (some resultHandle) (sourceScs ++ targetScs)))] := by
      cases result with
      | empty => exact False.elim (nonempty rfl)
      | reference name => rfl
      | node entry edges depth free => rfl
      | union entry members depth free => rfl
      | mu entry body depthShape ordinaryShape => rfl
    refine ⟨assimilated before target source (.unenumerated (some resultHandle) (sourceScs ++ targetScs)),
      raw, rfl, ?_, ?_, ?_⟩
    · simpa only [assimilated, List.getElem?_set_ne (Ne.symm different)] using middleStored
    · exact List.getElem?_set_self (by simpa only [List.length_set] using sourceInside)
    · intro slot node scs stored
      change ((before.values.set target (.unenumerated (some resultHandle) (sourceScs ++ targetScs))).set
        source .eliminated)[slot]? = some (.unenumerated (some node) scs) at stored
      obtain old | fresh := List.mem_or_eq_of_mem_set (List.mem_of_getElem? stored)
      · obtain ⟨oldSlot, oldStored⟩ := List.getElem?_of_mem old
        exact middleRealized oldSlot node scs oldStored
      · cases fresh

end MicroCFTA.SourcePruningEnumerationFinish
