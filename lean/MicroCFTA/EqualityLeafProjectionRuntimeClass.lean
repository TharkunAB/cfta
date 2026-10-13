import MicroCFTA.EqualityLeafProjectionSnapshotTargets
import MicroCFTA.EqualityLeafProjectionRuntimeForest

/-!
# Actual equality-class execution over projected leaf domains

The class builds every physical target from one original forest. The
simultaneous edit then runs in the actual target cache. A trimmed witness
for the result remains in that edit's actual output cache.
-/
namespace MicroCFTA.EqualityLeafProjectionRuntimeClass
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionWorkers (bindOptional)
open EqualityLeafProjectionSyntax (Path Tree Endpoints ChildAt Progress forestWeight)
open EqualityLeafProjectionCompile (Tag)
open EqualityRawLeafInventory (Leaf rank)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Execute the source class snapshot and then its simultaneous physical edits. -/
noncomputable def sourceClass (paths : List Path) (values : List (Value (Fin symbols) ConstraintKey)) :
    Work (Fin symbols) ConstraintKey (Option (List (Value (Fin symbols) ConstraintKey))) :=
  bindOptional (EqualityLeafProjectionSnapshotTargets.targets paths paths values) fun edits =>
    EqualityLeafProjectionWorkers.editChildren EqualityRawLeafProduct.intersect edits 0 values

/-- A complete actual source class decreases the occurrence potential and preserves every endpoint. -/
theorem class_progress (paths : List Path)
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (proper : ∀ path ∈ paths, path ≠ []) (endpoints : Endpoints paths forest)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (values : List (Value (Fin symbols) ConstraintKey)) (represented : RepresentsForest build forest state values) :
    let actual := run (sourceClass paths values) state
    Facts actual.2 ∧ ∃ results trimmed, actual.1 = some results ∧ RepresentsForest build trimmed actual.2 results ∧
      Progress (forestWeight rank) trimmed forest ∧
      (∀ offset path, ChildAt offset path forest → ChildAt offset path trimmed) ∧
      (results.map Value.referenceOf ≠ values.map Value.referenceOf → forestWeight rank trimmed < forestWeight rank forest) := by
  let targets := run (EqualityLeafProjectionSnapshotTargets.targets paths paths values) state
  obtain ⟨edits, targetFacts, targetPaths, targetReturned, targetRepresented⟩ :=
    EqualityLeafProjectionSnapshotTargets.targets_actual paths paths forest proper endpoints values state facts represented
  have targetGrowth : Grows state targets.2 := (InternedConstructorTemplates.run_correct _ state facts.coherent.valid).2
  have forestLater := forest_grows build forest state targets.2 facts.coherent.valid targetGrowth values represented
  have admissible : ∀ offset path target,
      ((0 + offset) :: path, target) ∈ EqualityLeafProjectionEditRelabel.targets Prod.fst edits → ChildAt offset path forest := by
    intro offset path target member
    obtain ⟨⟨original, pair⟩, present, same⟩ := List.mem_map.mp member
    have samePath := (Prod.mk.inj same).1
    have selected : offset :: path ∈ paths := by
      rw [← targetPaths]
      exact List.mem_map.mpr ⟨(original, pair), present, by simpa only [Nat.zero_add] using samePath⟩
    exact endpoints (offset :: path) selected
  have edited := EqualityLeafProjectionRuntimeForest.edit_progress forest edits 0 admissible targets.2 targetFacts
    targetRepresented values forestLater
  simp only [sourceClass, bindOptional, run_bind, targetReturned]
  exact edited

end MicroCFTA.EqualityLeafProjectionRuntimeClass
