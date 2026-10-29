import MicroCFTA.SourcePruningEnumerationStorageProgress
import MicroCFTA.SourcePruningEnumerationCachedAssimilation

/-!
# Chosen-term cost through actual graph-slot assimilation

Replacing a pending graph handle retains that slot's cost.
Eliminating the distinct source removes its full assigned constructor count.
This does not prove that a complete generator run reaches this operation.
-/
namespace MicroCFTA.EnumerationStorageProgress
open Language EnumerationState EnumerationCorrectness
variable {Symbol Guard : Type}

/-- Assimilation of two graph slots removes exactly the source's cost. -/
theorem assimilated_graph_pendingSize (before : State Symbol Guard)
    (source target sourceHandle targetHandle mergedHandle : Nat)
    (sourceScs targetScs : List Suspended) (assignment : Nat → Term Symbol)
    (different : target ≠ source)
    (sourceStored : before.values[source]? = some (.unenumerated (some sourceHandle) sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated (some targetHandle) targetScs)) :
    pendingSize (assimilated before target source
        (.unenumerated (some mergedHandle) (sourceScs ++ targetScs))) assignment +
        NumberedTerms.size (assignment source) = pendingSize before assignment := by
  let middle : State Symbol Guard :=
    {before with values :=
      before.values.set target (.unenumerated (some mergedHandle) (sourceScs ++ targetScs))}
  have targetCost : pendingSize middle assignment = pendingSize before assignment := by
    have written := values_set_pendingSize before target
      (.unenumerated (some targetHandle) targetScs)
      (.unenumerated (some mergedHandle) (sourceScs ++ targetScs)) assignment targetStored
    change pendingSize middle assignment + NumberedTerms.size (assignment target) =
      pendingSize before assignment + NumberedTerms.size (assignment target) at written
    omega
  have sourceStill : middle.values[source]? =
      some (.unenumerated (some sourceHandle) sourceScs) := by
    simpa only [middle, List.getElem?_set_ne different] using sourceStored
  have removed := values_set_pendingSize middle source
    (.unenumerated (some sourceHandle) sourceScs) .eliminated assignment sourceStill
  change pendingSize (assimilated before target source
      (.unenumerated (some mergedHandle) (sourceScs ++ targetScs))) assignment +
      NumberedTerms.size (assignment source) = pendingSize middle assignment + 0 at removed
  simpa only [targetCost, Nat.add_zero] using removed

/-- The actual union action retains every value slot and its assigned cost. -/
theorem unionVariables_pendingSize (fuel left right : Nat) (before after : State Symbol Guard)
    (assignment : Nat → Term Symbol)
    (success : Success (unionVariables fuel left right) before () after) :
    pendingSize after assignment = pendingSize before assignment := by
  obtain ⟨_forest, _joined, rfl⟩ :=
    (EnumerationSchedule.unionVariables_success fuel left right before after).mp success
  rfl

end MicroCFTA.EnumerationStorageProgress

namespace MicroCFTA.SourcePruningEnumerationStorageProgress
open Language EnumerationState EnumerationCorrectness EnumerationStorageProgress
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {EnumGuard NativeGuard : Type}

private theorem native_write_core
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target : Nat) (value : UVarValue Symbol) (gained lost : List Suspended)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (observed : SourcePruningEnumerationNativeIndex.write heap fuel target value gained lost before =
      some after) :
    after.core = {before.core with values := before.core.values.set target value} := by
  simp only [SourcePruningEnumerationNativeIndex.write, Option.bind_eq_some_iff,
    Option.some.injEq] at observed
  obtain ⟨_flag, _classified, _removed, _removedCounts, _saved, _savedCounts, same⟩ := observed
  exact (congrArg (fun result => result.core) same).symm

/-- Actual successful cached graph assimilation removes the source's full cost. -/
theorem cached_assimilation_pendingSize
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel source target sourceHandle targetHandle mergedHandle : Nat)
    (sourceScs targetScs : List Suspended)
    (before after : EnumerationExpandableIndex.Cached Symbol Constraint)
    (assignment : Nat → Term Symbol) (different : target ≠ source)
    (sourceStored : before.core.values[source]? = some (.unenumerated (some sourceHandle) sourceScs))
    (targetStored : before.core.values[target]? = some (.unenumerated (some targetHandle) targetScs))
    (observed : SourcePruningEnumerationCachedAssimilation.finish heap fuel source target
      (some mergedHandle) sourceScs targetScs before = some ([((), after)], after)) :
    pendingSize after.core assignment + NumberedTerms.size (assignment source) =
      pendingSize before.core assignment := by
  unfold SourcePruningEnumerationCachedAssimilation.finish at observed
  split at observed
  · simp at observed
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at observed
    obtain ⟨middle, targetWritten, last, sourceWritten, same⟩ := observed
    have middleCore := native_write_core heap fuel target
      (.unenumerated (some mergedHandle) (sourceScs ++ targetScs)) [] [] before middle targetWritten
    have lastCore := native_write_core heap fuel source .eliminated [] [] middle last sourceWritten
    have valuesSame := congrArg (fun result => result.2.core.values) same
    change last.core.values = after.core.values at valuesSame
    rw [lastCore, middleCore] at valuesSame
    have costSame : pendingSize after.core assignment =
        pendingSize (assimilated before.core target source
          (.unenumerated (some mergedHandle) (sourceScs ++ targetScs))) assignment := by
      unfold pendingSize
      rw [← valuesSame]
      rfl
    rw [costSame]
    exact assimilated_graph_pendingSize before.core source target sourceHandle targetHandle
      mergedHandle sourceScs targetScs assignment different sourceStored targetStored

/-- Successful cached graph assimilation strictly lowers the pending cost. -/
theorem cached_assimilation_pendingSize_lt
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel source target sourceHandle targetHandle mergedHandle : Nat)
    (sourceScs targetScs : List Suspended)
    (before after : EnumerationExpandableIndex.Cached Symbol Constraint)
    (assignment : Nat → Term Symbol) (different : target ≠ source)
    (sourceStored : before.core.values[source]? = some (.unenumerated (some sourceHandle) sourceScs))
    (targetStored : before.core.values[target]? = some (.unenumerated (some targetHandle) targetScs))
    (observed : SourcePruningEnumerationCachedAssimilation.finish heap fuel source target
      (some mergedHandle) sourceScs targetScs before = some ([((), after)], after)) :
    pendingSize after.core assignment < pendingSize before.core assignment := by
  have removed := cached_assimilation_pendingSize heap fuel source target sourceHandle targetHandle
    mergedHandle sourceScs targetScs before after assignment different sourceStored targetStored observed
  have positive : 0 < NumberedTerms.size (assignment source) := by
    cases assignment source with
    | node symbol children => simp only [NumberedTerms.size]; omega
  omega

end MicroCFTA.SourcePruningEnumerationStorageProgress
