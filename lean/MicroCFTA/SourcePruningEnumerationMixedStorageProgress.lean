import MicroCFTA.SourcePruningEnumerationStorageAssimilationProgress

/-!
# Chosen-term cost through mixed equality and graph slots

Pure equality slots have zero graph cost.
A common assigned term controls transfer from a graph slot to a pure slot.
The actual cached operation retains its rejection and write branches.
-/
namespace MicroCFTA.EnumerationStorageProgress
open Language EnumerationState EnumerationCorrectness
variable {Symbol Guard : Type}

/-- Two literal writes give the complete pending cost balance for optional graph handles. -/
theorem assimilated_pendingSize_balance (before : State Symbol Guard)
    (source target : Nat) (sourceNode targetNode merged : Option Nat)
    (sourceScs targetScs : List Suspended) (assignment : Nat → Term Symbol)
    (different : target ≠ source)
    (sourceStored : before.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated targetNode targetScs)) :
    pendingSize (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))) assignment +
        (if sourceNode.isSome then NumberedTerms.size (assignment source) else 0) +
        (if targetNode.isSome then NumberedTerms.size (assignment target) else 0) =
      pendingSize before assignment +
        (if merged.isSome then NumberedTerms.size (assignment target) else 0) := by
  let middle : State Symbol Guard :=
    {before with values := before.values.set target (.unenumerated merged (sourceScs ++ targetScs))}
  have targetWritten := values_set_pendingSize before target
    (.unenumerated targetNode targetScs) (.unenumerated merged (sourceScs ++ targetScs)) assignment targetStored
  have sourceStill : middle.values[source]? = some (.unenumerated sourceNode sourceScs) := by
    simpa only [middle, List.getElem?_set_ne different] using sourceStored
  have sourceWritten := values_set_pendingSize middle source
    (.unenumerated sourceNode sourceScs) .eliminated assignment sourceStill
  cases sourceNode <;> cases targetNode <;> cases merged <;>
    simp [pendingSize, assimilated, middle] at targetWritten sourceWritten ⊢ <;> omega

/-- A common assigned term prevents cost growth when a supported optional handle is merged. -/
theorem assimilated_pendingSize_le (before : State Symbol Guard)
    (source target : Nat) (sourceNode targetNode merged : Option Nat)
    (sourceScs targetScs : List Suspended) (assignment : Nat → Term Symbol)
    (different : target ≠ source)
    (sourceStored : before.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated targetNode targetScs))
    (equal : assignment source = assignment target)
    (supported : merged.isSome = true → sourceNode.isSome = true ∨ targetNode.isSome = true) :
    pendingSize (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))) assignment ≤
      pendingSize before assignment := by
  have balance := assimilated_pendingSize_balance before source target sourceNode targetNode merged
    sourceScs targetScs assignment different sourceStored targetStored
  rw [equal] at balance
  cases sourceNode <;> cases targetNode <;> cases merged <;> simp_all <;> omega

/-- An incoming graph write charges only a formerly pure target slot. -/
theorem incoming_values_pendingSize (before after : State Symbol Guard) (target handle : Nat)
    (oldNode : Option Nat) (oldScs incomingScs : List Suspended) (assignment : Nat → Term Symbol)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (written : after.values = before.values.set target (.unenumerated (some handle) incomingScs)) :
    pendingSize after assignment = pendingSize before assignment +
      (if oldNode.isSome then 0 else NumberedTerms.size (assignment target)) := by
  have exactCost := values_set_pendingSize before target (.unenumerated oldNode oldScs)
    (.unenumerated (some handle) incomingScs) assignment stored
  cases oldNode <;> simp [pendingSize, written] at exactCost ⊢ <;> omega

end MicroCFTA.EnumerationStorageProgress

namespace MicroCFTA.SourcePruningEnumerationStorageProgress
open Language EnumerationState EnumerationCorrectness EnumerationStorageProgress
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

private theorem mixed_write_core
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel target : Nat) (value : UVarValue Symbol)
    (before after : EnumerationExpandableIndex.Cached Symbol Constraint)
    (observed : SourcePruningEnumerationNativeIndex.write heap fuel target value [] [] before = some after) :
    after.core = {before.core with values := before.core.values.set target value} := by
  simp only [SourcePruningEnumerationNativeIndex.write, Option.bind_eq_some_iff,
    Option.some.injEq] at observed
  obtain ⟨_flag, _classified, _removed, _removedCounts, _saved, _savedCounts, same⟩ := observed
  exact (congrArg (fun result => result.core) same).symm

/-- Actual optional cached assimilation cannot increase the common assignment's graph cost. -/
theorem cached_assimilation_pendingSize_le
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel source target : Nat)
    (sourceNode targetNode merged : Option Nat) (sourceScs targetScs : List Suspended)
    (before after : EnumerationExpandableIndex.Cached Symbol Constraint)
    (rows : List (Unit × EnumerationExpandableIndex.Cached Symbol Constraint))
    (assignment : Nat → Term Symbol) (different : target ≠ source)
    (sourceStored : before.core.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.core.values[target]? = some (.unenumerated targetNode targetScs))
    (equal : assignment source = assignment target)
    (supported : merged.isSome = true → sourceNode.isSome = true ∨ targetNode.isSome = true)
    (observed : SourcePruningEnumerationCachedAssimilation.finish heap fuel source target merged
      sourceScs targetScs before = some (rows, after)) :
    pendingSize after.core assignment ≤ pendingSize before.core assignment := by
  unfold SourcePruningEnumerationCachedAssimilation.finish at observed
  split at observed
  · have same := congrArg Prod.snd (Option.some.inj observed)
    change before = after at same
    rw [← same]
    exact Nat.le_refl _
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at observed
    obtain ⟨middle, targetWritten, last, sourceWritten, same⟩ := observed
    have middleCore := mixed_write_core heap fuel target
      (.unenumerated merged (sourceScs ++ targetScs)) before middle targetWritten
    have lastCore := mixed_write_core heap fuel source .eliminated middle last sourceWritten
    have valuesSame := congrArg (fun result => result.2.core.values) same
    change last.core.values = after.core.values at valuesSame
    rw [lastCore, middleCore] at valuesSame
    have costSame : pendingSize after.core assignment =
        pendingSize (assimilated before.core target source (.unenumerated merged (sourceScs ++ targetScs)))
          assignment := by
      unfold pendingSize
      rw [← valuesSame]
      rfl
    rw [costSame]
    exact assimilated_pendingSize_le before.core source target sourceNode targetNode merged
      sourceScs targetScs assignment different sourceStored targetStored equal supported

/-- An original semantic assignment supplies the equality required by mixed assimilation. -/
theorem cached_assimilation_pendingSize_of_model
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel source target : Nat)
    (sourceNode targetNode merged : Option Nat) (sourceScs targetScs : List Suspended)
    (before after : EnumerationExpandableIndex.Cached Symbol Constraint)
    (rows : List (Unit × EnumerationExpandableIndex.Cached Symbol Constraint))
    (language : NodeLanguage Symbol) (meaning : Constraint → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (different : target ≠ source)
    (sourceStored : before.core.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.core.values[target]? = some (.unenumerated targetNode targetScs))
    (satisfies : Satisfies language meaning assignment before.core)
    (joined : UnionFind.SameClass before.core.representatives source target)
    (supported : merged.isSome = true → sourceNode.isSome = true ∨ targetNode.isSome = true)
    (observed : SourcePruningEnumerationCachedAssimilation.finish heap fuel source target merged
      sourceScs targetScs before = some (rows, after)) :
    pendingSize after.core assignment ≤ pendingSize before.core assignment :=
  cached_assimilation_pendingSize_le heap fuel source target sourceNode targetNode merged
    sourceScs targetScs before after rows assignment different sourceStored targetStored
    (satisfies.1.1 source target joined) supported observed

end MicroCFTA.SourcePruningEnumerationStorageProgress
