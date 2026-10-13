import MicroCFTA.EqualityLeafProjectionRuntimeClass

/-!
# Source-ordered class schedules in actual runtime caches

The source applies the tail classes first. Each later class reads the
preceding physical result and starts from its actual output cache. The
same occurrence potential decreases across the complete schedule.
-/
namespace MicroCFTA.EqualityLeafProjectionRuntimeSchedule
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionWorkers (bindOptional)
open EqualityLeafProjectionSyntax (Path Tree Endpoints ChildAt Progress forestWeight)
open EqualityLeafProjectionCompile (Tag)
open EqualityRawLeafInventory (Leaf rank)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Run classes in the source right-fold order, with the actual intervening caches. -/
noncomputable def sourceSchedule (classes : List (List Path)) (values : List (Value (Fin symbols) ConstraintKey)) :
    Work (Fin symbols) ConstraintKey (Option (List (Value (Fin symbols) ConstraintKey))) :=
  match classes with
  | [] => .pure (some values)
  | paths :: rest => bindOptional (sourceSchedule rest values) (EqualityLeafProjectionRuntimeClass.sourceClass paths)

/-- Actual source class schedules preserve witnesses and strictly decrease on physical change. -/
theorem schedule_progress (classes : List (List Path))
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (proper : ∀ path ∈ classes.flatten, path ≠ []) (endpoints : Endpoints classes.flatten forest)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (values : List (Value (Fin symbols) ConstraintKey)) (represented : RepresentsForest build forest state values) :
    let actual := run (sourceSchedule classes values) state
    Facts actual.2 ∧ ∃ results trimmed, actual.1 = some results ∧ RepresentsForest build trimmed actual.2 results ∧
      Progress (forestWeight rank) trimmed forest ∧
      (∀ offset path, ChildAt offset path forest → ChildAt offset path trimmed) ∧
      (results.map Value.referenceOf ≠ values.map Value.referenceOf → forestWeight rank trimmed < forestWeight rank forest) := by
  induction classes generalizing forest state values with
  | nil => exact ⟨facts, values, forest, rfl, represented, EqualityLeafProjectionSyntax.progress_refl _ _,
      fun _ _ endpoint => endpoint, fun changed => False.elim (changed rfl)⟩
  | cons paths rest ih =>
      have restProper : ∀ path ∈ rest.flatten, path ≠ [] := fun path member => proper path (by simp [member])
      have restEndpoints : Endpoints rest.flatten forest := fun path member => endpoints path (by simp [member])
      let tail := run (sourceSchedule rest values) state
      obtain ⟨tailFacts, middleValues, middle, tailReturned, tailRepresented, tailProgress, tailEndpoints, _⟩ :=
        ih forest restProper restEndpoints state facts values represented
      have headProper : ∀ path ∈ paths, path ≠ [] := fun path member => proper path (by simp [member])
      have headEndpoints : Endpoints paths middle := by
        intro path member
        cases path with
        | nil => trivial
        | cons index path => exact tailEndpoints index path (endpoints (index :: path) (by simp [member]))
      obtain ⟨headFacts, results, trimmed, headReturned, headRepresented, headProgress, headEndpoints, _⟩ :=
        EqualityLeafProjectionRuntimeClass.class_progress paths middle headProper headEndpoints
          tail.2 tailFacts middleValues tailRepresented
      have executed : run (sourceSchedule (paths :: rest) values) state =
          run (EqualityLeafProjectionRuntimeClass.sourceClass paths middleValues) tail.2 := by
        simp only [sourceSchedule, bindOptional, run_bind, tailReturned]
        rfl
      have progress := EqualityLeafProjectionSyntax.progress_trans (forestWeight rank) forest middle trimmed tailProgress headProgress
      have output : RepresentsForest build trimmed (run (sourceSchedule (paths :: rest) values) state).2 results := by
        rw [executed]
        exact headRepresented
      have strict := EqualityLeafProjectionRuntimeForest.physical_strict forest trimmed (sourceSchedule (paths :: rest) values)
        state facts values results represented output progress
      rw [executed]
      exact ⟨headFacts, results, trimmed, headReturned, headRepresented, progress,
        fun index path endpoint => headEndpoints index path (tailEndpoints index path endpoint), strict⟩

end MicroCFTA.EqualityLeafProjectionRuntimeSchedule
