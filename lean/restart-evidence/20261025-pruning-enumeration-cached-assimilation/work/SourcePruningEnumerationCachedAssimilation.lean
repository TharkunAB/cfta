import MicroCFTA.SourcePruningEnumerationNativeIndex
import MicroCFTA.SourcePruningEnumerationFoldInvariants

namespace MicroCFTA.SourcePruningEnumerationCachedAssimilation
open EnumerationState EnumerationSchedule EnumerationCorrectness
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Reject Empty or apply both native writes and then combine recursion ancestry. -/
def finish
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel source target : Nat)
    (merged : Option Nat) (sourceScs targetScs : List EnumerationState.Suspended)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) :
    Option (List (Unit × EnumerationExpandableIndex.Cached Symbol Constraint) ×
      EnumerationExpandableIndex.Cached Symbol Constraint) :=
  if merged = some 0 then some ([], before) else
    (SourcePruningEnumerationNativeIndex.write heap fuel target
      (.unenumerated merged (sourceScs ++ targetScs)) [] [] before).bind fun targetAfter =>
      (SourcePruningEnumerationNativeIndex.write heap fuel source .eliminated [] [] targetAfter).map fun sourceAfter =>
        let finished : EnumerationExpandableIndex.Cached Symbol Constraint :=
          EnumerationExpandableIndex.frame
            {sourceAfter.core with recursionAncestry := fun other =>
              if other = target then
                (sourceAfter.core.recursionAncestry source ++ sourceAfter.core.recursionAncestry target).eraseDups
              else sourceAfter.core.recursionAncestry other} sourceAfter
        ([((), finished)], finished)

/-- Derive exact cached assimilation and preserve each completed index and storage law. -/
theorem complete
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) (source target : Nat)
    (sourceNode targetNode merged : Option Nat)
    (sourceScs targetScs : List EnumerationState.Suspended) (roots : Nat → Nat)
    (storage : StorageValid before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (sourceStored : before.core.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.core.values[target]? = some (.unenumerated targetNode targetScs))
    (different : target ≠ source)
    (mergedRealized : ∀ (handle : Nat), merged = some handle →
      ∃ (value : InternedConstructorTemplates.Value Symbol Constraint),
        lookupNode heap handle = some value ∧ InternedProbeProvenance.Available heap value ∧ value.free = []) :
    ∃ (rows : List (Unit × EnumerationExpandableIndex.Cached Symbol Constraint))
      (after : EnumerationExpandableIndex.Cached Symbol Constraint),
      (∀ (fuel : Nat), finish heap fuel source target merged sourceScs targetScs before = some (rows, after)) ∧
      ExceptT.run (SourcePruningEnumerationDispatch.finishOptional (EnumGuard := Constraint)
        source target merged sourceScs targetScs before.core) =
          rows.map (fun row => .ok (row.1, row.2.core)) ∧
      after.core.counter = before.core.counter ∧
      after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
      StorageValid after.core ∧ PendingRealized heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      after.waiting = before.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      (if merged = some 0 then rows = [] ∧ after = before else
        rows = [((), after)] ∧
        after.core = assimilated before.core target source (.unenumerated merged (sourceScs ++ targetScs)) ∧
        after.core.values[source]? = some .eliminated ∧
        after.core.values[target]? = some (.unenumerated merged (sourceScs ++ targetScs)) ∧
        after.expandable source = false ∧
        (∀ (slot : Nat), slot ≠ source → slot ≠ target → after.expandable slot = before.expandable slot)) := by
  by_cases empty : merged = some 0
  · refine ⟨[], before, ?_, ?_, rfl, rfl, paths, storage, realized, counts, rfl, flags, ?_⟩
    · intro fuel
      simp only [finish, ite_eq_left empty]
    · change (if merged = some 0 then [] else
        [Except.ok ((), assimilated before.core target source
          (.unenumerated merged (sourceScs ++ targetScs)))]) = []
      rw [ite_eq_left empty]
    · rw [ite_eq_left empty]
      exact ⟨rfl, rfl⟩
  ·
    have sourceInside : source < before.core.values.length := by
      exact (List.getElem?_eq_some_iff.mp sourceStored).elim (fun bound _elementEquality => bound)
    have targetInside : target < before.core.values.length := by
      exact (List.getElem?_eq_some_iff.mp targetStored).elim (fun bound _elementEquality => bound)
    have candidateExists : ∃ (flag : Bool),
      SourcePruningEnumerationNativeIndex.candidate heap
        (.unenumerated merged (sourceScs ++ targetScs)) = some flag := by
      cases merged with
      | none => exact ⟨false, rfl⟩
      | some handle =>
        obtain ⟨value, decoded, _available, _closed⟩ := mergedRealized handle rfl
        exact ⟨!(MergedOrdinaryHeight.recursiveBoundary value && (sourceScs ++ targetScs).isEmpty),
          by simp only [SourcePruningEnumerationNativeIndex.candidate, decoded, Option.map_some]⟩
    obtain ⟨flag, classified⟩ := candidateExists
    obtain ⟨afterStorage, afterCounts⟩ :=
      SourcePruningEnumerationFoldInvariants.assimilated_preserves before.core source target
        sourceNode targetNode merged sourceScs targetScs roots before.waiting
        storage counts sourceStored targetStored different
    have finalRealized : PendingRealized heap
      (assimilated before.core target source (.unenumerated merged (sourceScs ++ targetScs))) := by
      intro slot node scs stored
      by_cases atSource : slot = source
      · subst slot
        simp only [assimilated,
          List.getElem?_set_self
            (l := before.core.values.set target (.unenumerated merged (sourceScs ++ targetScs)))
            (a := (UVarValue.eliminated : UVarValue Symbol))
            (by simpa only [List.length_set] using sourceInside)] at stored
        cases stored
      · by_cases atTarget : slot = target
        · subst slot
          simp only [assimilated, List.getElem?_set_ne (Ne.symm different),
            List.getElem?_set_self targetInside, Option.some.injEq,
            UVarValue.unenumerated.injEq] at stored
          exact mergedRealized node stored.1
        · exact realized slot node scs (by
            simpa only [assimilated, List.getElem?_set_ne (Ne.symm atSource),
              List.getElem?_set_ne (Ne.symm atTarget)] using stored)
    have finalFlags : ∀ (slot : Nat),
      SourcePruningEnumerationNativeIndex.candidate heap
        (((assimilated before.core target source
          (.unenumerated merged (sourceScs ++ targetScs))).values[slot]?).getD .eliminated) =
        some (if slot = source then false else if slot = target then flag else before.expandable slot) := by
      intro slot
      by_cases atSource : slot = source
      · subst slot
        simp only [assimilated,
          List.getElem?_set_self
            (l := before.core.values.set target (.unenumerated merged (sourceScs ++ targetScs)))
            (a := (UVarValue.eliminated : UVarValue Symbol))
            (by simpa only [List.length_set] using sourceInside),
          Option.getD_some, SourcePruningEnumerationNativeIndex.candidate, ↓reduceIte]
      · by_cases atTarget : slot = target
        · subst slot
          simpa only [assimilated, List.getElem?_set_ne (Ne.symm different),
            List.getElem?_set_self targetInside, Option.getD_some, ite_eq_right different, ↓reduceIte]
            using classified
        · simpa only [assimilated, List.getElem?_set_ne (Ne.symm atSource),
            List.getElem?_set_ne (Ne.symm atTarget), ite_eq_right atSource, ite_eq_right atTarget]
            using flags slot
    let after : EnumerationExpandableIndex.Cached Symbol Constraint :=
      ⟨assimilated before.core target source (.unenumerated merged (sourceScs ++ targetScs)),
        fun slot => if slot = source then false else if slot = target then flag else before.expandable slot,
        before.waiting⟩
    refine ⟨[((), after)], after, ?_, ?_, rfl, rfl, paths, afterStorage, finalRealized,
      afterCounts, rfl, finalFlags, ?_⟩
    · intro fuel
      simp only [finish, ite_eq_right empty, SourcePruningEnumerationNativeIndex.write,
        classified, SourcePruningEnumerationNativeIndex.count, Option.bind_some]
      rfl
    · change (if merged = some 0 then [] else
        [Except.ok ((), assimilated before.core target source
          (.unenumerated merged (sourceScs ++ targetScs)))]) = [Except.ok ((), after.core)]
      rw [ite_eq_right empty]
    · rw [ite_eq_right empty]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
      · exact List.getElem?_set_self (by simpa only [List.length_set] using sourceInside)
      · simpa only [after, assimilated, List.getElem?_set_ne (Ne.symm different)] using
          (List.getElem?_set_self targetInside
            (a := (UVarValue.unenumerated merged (sourceScs ++ targetScs) : UVarValue Symbol)))
      · simp only [after, ↓reduceIte]
      · intro slot notSource notTarget
        simp only [after, ite_eq_right notSource, ite_eq_right notTarget]

end MicroCFTA.SourcePruningEnumerationCachedAssimilation
