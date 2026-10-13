import MicroCFTA.MergedProjectionSchedule
import MicroCFTA.EqualityLeafProjectionRuntimeEmpty

/-!
# Merged equality passes in actual runtime caches

The pass keeps the source skip and contradiction branches. Its ordinary
branch requires paths, applies the class right fold, and propagates empty
roots. Physical identity change strictly decreases a finite occurrence
potential without carrying proof preparation into the runtime state.
-/
namespace MicroCFTA.MergedProjectionPass
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionWorkers (bindOptional)
open EqualityLeafProjectionSyntax (Path Tree Endpoints ChildAt Progress forestWeight)
open EqualityLeafProjectionCompile (Tag)
open EqualityRawLeafInventory (Leaf rank)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)
open EqualityLeafProjectionRuntimeEmpty (erase propagate)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Execute one source equality pass with its actual branch and phase order. -/
noncomputable def sourcePass (order : Value (Fin symbols) ConstraintKey → List (Fin symbols))
    (skip contradiction : Bool) (classes : List (List Path))
    (values : List (Value (Fin symbols) ConstraintKey)) :
    Work (Fin symbols) ConstraintKey (Option (List (Value (Fin symbols) ConstraintKey))) :=
  if skip then .pure (some values) else if contradiction then .pure (some (erase values)) else
    bindOptional (EqualityLeafProjectionWorkers.requireChildren classes.flatten 0 values) fun required =>
      bindOptional (MergedProjectionSchedule.sourceSchedule order classes required) fun narrowed =>
        .pure (some (propagate narrowed))

/-- Every actual pass has a runtime-cache witness and strictly decreases on changed physical identities. -/
theorem pass_progress (order : Value (Fin symbols) ConstraintKey → List (Fin symbols))
    (complete : MergedProjectionTargets.CompleteOrder order) (skip contradiction : Bool) (classes : List (List Path))
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (proper : ∀ path ∈ classes.flatten, path ≠ []) (endpoints : Endpoints classes.flatten forest)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (values : List (Value (Fin symbols) ConstraintKey)) (represented : RepresentsForest build forest state values) :
    let actual := run (sourcePass order skip contradiction classes values) state
    Facts actual.2 ∧ ∃ results trimmed, actual.1 = some results ∧ RepresentsForest build trimmed actual.2 results ∧
      Progress (forestWeight rank) trimmed forest ∧
      (∀ offset path, ChildAt offset path forest → ChildAt offset path trimmed) ∧
      (results.map Value.referenceOf ≠ values.map Value.referenceOf → forestWeight rank trimmed < forestWeight rank forest) := by
  cases skip with
  | true => exact ⟨facts, values, forest, rfl, represented, EqualityLeafProjectionSyntax.progress_refl _ _,
      fun _ _ endpoint => endpoint, fun changed => False.elim (changed rfl)⟩
  | false =>
      cases contradiction with
      | true =>
          have erased := EqualityLeafProjectionRuntimeEmpty.erase_progress forest state facts values represented
          exact ⟨facts, erase values, _, rfl, erased.1, erased.2.1,
            fun index path _ => erased.2.2.1 index path, erased.2.2.2⟩
      | false =>
          let required := run (EqualityLeafProjectionWorkers.requireChildren classes.flatten 0 values) state
          obtain ⟨requiredFacts, requiredValues, requiredForest, requiredReturned, requiredRepresented,
              requiredProgress, requiredEndpoints, _⟩ :=
            EqualityLeafProjectionRuntimeForest.require_progress forest classes.flatten 0 state facts values represented
          have neededEndpoints : Endpoints classes.flatten requiredForest := by
            intro path member
            cases path with
            | nil => trivial
            | cons index path => exact requiredEndpoints index path (endpoints (index :: path) member)
          let scheduled := run (MergedProjectionSchedule.sourceSchedule order classes requiredValues) required.2
          obtain ⟨scheduledFacts, scheduledValues, scheduledForest, scheduledReturned, scheduledRepresented,
              scheduledProgress, scheduledEndpoints, _⟩ :=
            MergedProjectionSchedule.schedule_progress order complete classes requiredForest proper neededEndpoints
              required.2 requiredFacts requiredValues requiredRepresented
          obtain ⟨trimmed, propagatedRepresented, propagatedProgress, propagatedEndpoints, _⟩ :=
            EqualityLeafProjectionRuntimeEmpty.propagate_progress scheduledForest scheduled.2 scheduledFacts
              scheduledValues scheduledRepresented
          have progress := EqualityLeafProjectionSyntax.progress_trans (forestWeight rank) forest requiredForest trimmed requiredProgress
            (EqualityLeafProjectionSyntax.progress_trans (forestWeight rank) requiredForest scheduledForest trimmed scheduledProgress propagatedProgress)
          have executed : run (sourcePass order false false classes values) state =
              (some (propagate scheduledValues), scheduled.2) := by
            dsimp only [required] at scheduledReturned
            simp only [sourcePass, Bool.false_eq_true, ↓reduceIte, bindOptional, run_bind,
              requiredReturned, scheduledReturned, run]
            rfl
          have output : RepresentsForest build trimmed (run (sourcePass order false false classes values) state).2 (propagate scheduledValues) := by
            rw [executed]
            exact propagatedRepresented
          have strict := EqualityLeafProjectionRuntimeForest.physical_strict forest trimmed (sourcePass order false false classes values)
            state facts values (propagate scheduledValues) represented output progress
          rw [executed]
          exact ⟨scheduledFacts, propagate scheduledValues, trimmed, rfl, propagatedRepresented, progress,
            fun index path endpoint => propagatedEndpoints index path (scheduledEndpoints index path (requiredEndpoints index path endpoint)), strict⟩

end MicroCFTA.MergedProjectionPass
