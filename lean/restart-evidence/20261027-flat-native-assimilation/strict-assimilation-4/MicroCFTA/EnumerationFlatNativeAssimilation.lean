import MicroCFTA.EnumerationFlatNativeIndex
import MicroCFTA.EnumerationFlatBounds
import MicroCFTA.SourcePruningEnumerationCachedAssimilation

/-!
# Completed native assimilation with direct-parent forests

Both raw writes use empty count deltas. Correspondence holds at every old
fuel. Canonical counts are required only after the completed pair of writes.
-/

namespace MicroCFTA.EnumerationFlatNativeAssimilation

open EnumerationFlatCached
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Reject Empty or write target, eliminate source and then combine ancestry. -/
def finish (heap : InternedConstructorTemplates.State Symbol Constraint)
    (source target : Nat) (merged : Option Nat)
    (sourceScs targetScs : List EnumerationState.Suspended) (before : Cached Symbol Constraint) :
    Option (List (Unit × Cached Symbol Constraint) × Cached Symbol Constraint) :=
  if merged = some 0 then some ([], before) else
    (EnumerationFlatNativeIndex.write heap target
      (.unenumerated merged (sourceScs ++ targetScs)) [] [] before).bind fun targetAfter =>
      (EnumerationFlatNativeIndex.write heap source .eliminated [] [] targetAfter).map fun sourceAfter =>
        let finished := frame
          {sourceAfter.core with recursionAncestry := fun other =>
            if other = target then
              (sourceAfter.core.recursionAncestry source ++ sourceAfter.core.recursionAncestry target).eraseDups
            else sourceAfter.core.recursionAncestry other} sourceAfter
        ([((), finished)], finished)

/-- Optional cached runs retain every ordered row and the actual outer cache. -/
def ResultRelated (flat : Option (List (Unit × Cached Symbol Constraint) × Cached Symbol Constraint))
    (earlier : Option (List (Unit × EnumerationExpandableIndex.Cached Symbol Constraint) ×
      EnumerationExpandableIndex.Cached Symbol Constraint)) : Prop :=
  match flat, earlier with
  | none, none => True
  | some (rows, after), some (oldRows, oldAfter) =>
      EnumerationResultRelation.Results (Error := EnumerationState.Error) Related
        (rows.map Except.ok) (oldRows.map Except.ok) ∧ Related after oldAfter
  | _, _ => False

/-- Empty-delta assimilation retains the complete observation at every earlier fuel. -/
theorem finish_related (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel source target : Nat)
    (merged : Option Nat) (sourceScs targetScs : List EnumerationState.Suspended) :
    ResultRelated (finish heap source target merged sourceScs targetScs flat)
      (SourcePruningEnumerationCachedAssimilation.finish heap fuel source target
        merged sourceScs targetScs earlier) := by
  by_cases empty : merged = some 0
  · simp only [finish, SourcePruningEnumerationCachedAssimilation.finish, empty, ↓reduceIte]
    exact ⟨.nil, related⟩
  · cases classified : SourcePruningEnumerationNativeIndex.candidate heap
      (.unenumerated merged (sourceScs ++ targetScs)) with
    | none =>
        simp [finish, SourcePruningEnumerationCachedAssimilation.finish, empty,
          EnumerationFlatNativeIndex.write, SourcePruningEnumerationNativeIndex.write,
          classified, ResultRelated]
    | some flag =>
        have eliminated : SourcePruningEnumerationNativeIndex.candidate heap
            (.eliminated : EnumerationState.UVarValue Symbol) = some false := rfl
        simp only [finish, SourcePruningEnumerationCachedAssimilation.finish, empty, ↓reduceIte,
          EnumerationFlatNativeIndex.write, SourcePruningEnumerationNativeIndex.write,
          classified, eliminated,
          SourcePruningEnumerationNativeIndex.count, Option.bind_some, Option.map_some]
        have cores : EnumerationFlatState.Related
            {flat.core with
              values := (flat.core.values.set target (.unenumerated merged (sourceScs ++ targetScs))).set source .eliminated
              recursionAncestry := fun other => if other = target then
                (flat.core.recursionAncestry source ++ flat.core.recursionAncestry target).eraseDups
                else flat.core.recursionAncestry other}
            {earlier.core with
              values := (earlier.core.values.set target (.unenumerated merged (sourceScs ++ targetScs))).set source .eliminated
              recursionAncestry := fun other => if other = target then
                (earlier.core.recursionAncestry source ++ earlier.core.recursionAncestry target).eraseDups
                else earlier.core.recursionAncestry other} := by
          refine ⟨related.core.valid, related.core.representatives, related.core.counter,
            ?_, related.core.obligations, ?_, related.core.expansionAncestry⟩
          · rw [related.core.values]
          · rw [related.core.recursionAncestry]
        have final : Related
            ⟨_, (fun uv => if uv = source then false else if uv = target then flag else flat.expandable uv), flat.waiting⟩
            ⟨_, (fun uv => if uv = source then false else if uv = target then flag else earlier.expandable uv), earlier.waiting⟩ :=
          ⟨cores, by rw [related.expandable], related.waiting⟩
        exact ⟨.cons (.ok () final) .nil, final⟩

/-- Completed distinct pending-slot assimilation derives both native index laws. -/
theorem finish_correct (heap : InternedConstructorTemplates.State Symbol Constraint)
    (before after : Cached Symbol Constraint) (correct : EnumerationFlatNativeIndex.Correct heap before)
    (source target : Nat) (sourceNode targetNode merged : Option Nat)
    (sourceScs targetScs : List EnumerationState.Suspended)
    (sourceStored : before.core.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.core.values[target]? = some (.unenumerated targetNode targetScs))
    (different : target ≠ source)
    (done : finish heap source target merged sourceScs targetScs before = some (rows, after)) :
    EnumerationFlatNativeIndex.Correct heap after := by
  by_cases empty : merged = some 0
  · simp [finish, empty] at done
    exact done.2 ▸ correct
  · cases classified : SourcePruningEnumerationNativeIndex.candidate heap
      (.unenumerated merged (sourceScs ++ targetScs)) with
    | none => simp [finish, empty, EnumerationFlatNativeIndex.write, classified] at done
    | some flag =>
        have eliminated : SourcePruningEnumerationNativeIndex.candidate heap
            (.eliminated : EnumerationState.UVarValue Symbol) = some false := rfl
        simp [finish, empty, EnumerationFlatNativeIndex.write, classified,
          eliminated,
          EnumerationFlatNativeIndex.count, EnumerationCanonicalWaiting.count,
          EnumerationWaitingIndex.count, frame] at done
        obtain ⟨_rows, same⟩ := done
        subst after
        refine ⟨by simpa using correct.aligned, ?_, ?_⟩
        · intro uv
          have sourceInside := (List.getElem?_eq_some_iff.mp sourceStored).1
          have targetInside := (List.getElem?_eq_some_iff.mp targetStored).1
          by_cases atSource : uv = source
          · subst uv
            simp [sourceInside, SourcePruningEnumerationNativeIndex.candidate]
          · by_cases atTarget : uv = target
            · subst uv
              simpa [List.getElem?_set_ne (Ne.symm different),
                List.getElem?_set_self targetInside, Option.getD_some,
                different] using classified
            · simpa [List.getElem?_set_ne (Ne.symm atSource),
                List.getElem?_set_ne (Ne.symm atTarget), atSource, atTarget]
                using correct.expandable uv
        · exact EnumerationCanonicalWaiting.assimilation_correct
            (FlatUnionFind.root before.core.representatives) before.core.values target source
            (.unenumerated sourceNode sourceScs) (.unenumerated targetNode targetScs)
            (.unenumerated merged (sourceScs ++ targetScs)) different sourceStored targetStored rfl
            before.waiting correct.waiting

/-- Successful assimilation retains supply, forest, waiting table and residual guards. -/
theorem finish_fields (heap : InternedConstructorTemplates.State Symbol Constraint)
    (before after : Cached Symbol Constraint) (source target : Nat) (merged : Option Nat)
    (sourceScs targetScs : List EnumerationState.Suspended)
    (done : finish heap source target merged sourceScs targetScs before = some (rows, after)) :
    after.core.counter = before.core.counter ∧
      after.core.representatives = before.core.representatives ∧
      after.waiting = before.waiting ∧ after.core.obligations = before.core.obligations := by
  by_cases empty : merged = some 0
  · simp [finish, empty] at done
    subst after
    exact ⟨rfl, rfl, rfl, rfl⟩
  · cases classified : SourcePruningEnumerationNativeIndex.candidate heap
      (.unenumerated merged (sourceScs ++ targetScs)) with
    | none => simp [finish, empty, EnumerationFlatNativeIndex.write, classified] at done
    | some flag =>
        have eliminated : SourcePruningEnumerationNativeIndex.candidate heap
            (.eliminated : EnumerationState.UVarValue Symbol) = some false := rfl
        simp [finish, empty, EnumerationFlatNativeIndex.write, classified, eliminated,
          EnumerationFlatNativeIndex.count, EnumerationCanonicalWaiting.count,
          EnumerationWaitingIndex.count, frame] at done
        obtain ⟨_rows, same⟩ := done
        subst after
        exact ⟨rfl, rfl, rfl, rfl⟩

/-- Successful assimilation retains the separately established explicit-key bound. -/
theorem finish_bounded (heap : InternedConstructorTemplates.State Symbol Constraint)
    (before after : Cached Symbol Constraint) (bounded : EnumerationFlatState.Bounded before.core)
    (source target : Nat) (merged : Option Nat)
    (sourceScs targetScs : List EnumerationState.Suspended)
    (done : finish heap source target merged sourceScs targetScs before = some (rows, after)) :
    EnumerationFlatState.Bounded after.core := by
  obtain ⟨counter, forest, _waiting, _guards⟩ :=
    finish_fields heap before after source target merged sourceScs targetScs done
  simpa only [EnumerationFlatState.Bounded, forest, counter] using bounded

/-- Actual decoded merged handles give a completed run and correct final native indexes. -/
theorem finish_complete (heap : InternedConstructorTemplates.State Symbol Constraint)
    (before : Cached Symbol Constraint) (correct : EnumerationFlatNativeIndex.Correct heap before)
    (source target : Nat) (sourceNode targetNode merged : Option Nat)
    (sourceScs targetScs : List EnumerationState.Suspended)
    (sourceStored : before.core.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.core.values[target]? = some (.unenumerated targetNode targetScs))
    (different : target ≠ source)
    (decoded : ∀ handle, merged = some handle → handle ≠ 0 →
      ∃ value, SourcePruningEnumerationNodes.lookupNode heap handle = some value) :
    ∃ rows after, finish heap source target merged sourceScs targetScs before = some (rows, after) ∧
      EnumerationFlatNativeIndex.Correct heap after ∧
      after.core.counter = before.core.counter ∧
      after.core.representatives = before.core.representatives ∧ after.waiting = before.waiting ∧
      (EnumerationFlatState.Bounded before.core → EnumerationFlatState.Bounded after.core) := by
  have completed : ∃ rows after,
      finish heap source target merged sourceScs targetScs before = some (rows, after) := by
    by_cases empty : merged = some 0
    · exact ⟨[], before, by simp [finish, empty]⟩
    · have classifiable : ∃ flag, SourcePruningEnumerationNativeIndex.candidate heap
          (.unenumerated merged (sourceScs ++ targetScs)) = some flag := by
        cases merged with
        | none => exact ⟨false, rfl⟩
        | some handle =>
            have nonzero : handle ≠ 0 := by intro zero; subst handle; exact empty rfl
            obtain ⟨value, found⟩ := decoded handle rfl nonzero
            exact ⟨_, by simp only [SourcePruningEnumerationNativeIndex.candidate, found, Option.map_some]⟩
      obtain ⟨flag, classified⟩ := classifiable
      have eliminated : SourcePruningEnumerationNativeIndex.candidate heap
          (.eliminated : EnumerationState.UVarValue Symbol) = some false := rfl
      simp only [finish, empty, ↓reduceIte, EnumerationFlatNativeIndex.write, classified,
        eliminated, Option.map_some, Option.bind_some]
      exact ⟨_, _, rfl⟩
  obtain ⟨rows, after, done⟩ := completed
  obtain ⟨counter, forest, waiting, _guards⟩ :=
    finish_fields heap before after source target merged sourceScs targetScs done
  exact ⟨rows, after, done,
    finish_correct heap before after correct source target sourceNode targetNode merged
      sourceScs targetScs sourceStored targetStored different done,
    counter, forest, waiting, fun bounded =>
      finish_bounded heap before after bounded source target merged sourceScs targetScs done⟩

end MicroCFTA.EnumerationFlatNativeAssimilation
