import MicroCFTA.EqualityLeafProjectionTargetFold
import MicroCFTA.EqualityRawLeafPullback

/-!
# Leaf representations in actual source output caches

Projection and target folds run before their finite representations are
proved. Raw leaf pullback removes all temporary proof preparation. The
next runtime operation starts from the actual preceding output cache.
-/
namespace MicroCFTA.EqualityLeafProjectionRuntimeLeaves
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionPathWorker EqualityLeafProjectionPathInputs
open EqualityRawLeafInventory (Leaf intersect)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)
open EqualityLeafProjectionSyntax (Path ChildAt)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- An actual endpoint projection has a finite representation in its own runtime output cache. -/
theorem read_actual (path : Path) (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (value : Value (Fin symbols) ConstraintKey) (input : Input (build (initial := initial)) path state value) :
    let actual := run (read path value) state
    ∃ leaf : Leaf initial symbols, ∃ result,
      Facts actual.2 ∧ actual.1 = some result ∧ Represents build (.leaf leaf) actual.2 result := by
  obtain ⟨after, leaf, result, afterFacts, _, returned, represented⟩ :=
    EqualityLeafProjectionPathExact.read_completed path state facts value input
  obtain ⟨tree, _, inputRepresented⟩ := input
  have available := EqualityLeafProjectionRepresentation.available build EqualityRawLeafCompiler.leaves_available
    tree state facts value inputRepresented
  have checked := read_available path value state facts available
  exact ⟨leaf, result, checked.1, returned,
    EqualityRawLeafPullback.represented_pullback leaf _ after checked.1 afterFacts result
      (checked.2 result returned).resident represented⟩

/-- Nonempty forest paths retain their finite result directly in the runtime cache. -/
theorem forest_read_actual
    (forest : List (EqualityLeafProjectionSyntax.Tree
      (EqualityLeafProjectionCompile.Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (index : Nat) (path : Path) (endpoints : ChildAt index path forest)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (values : List (Value (Fin symbols) ConstraintKey))
    (represented : RepresentsForest build forest state values) :
    let actual := run (readForest (index :: path) values) state
    ∃ leaf : Leaf initial symbols, ∃ result,
      Facts actual.2 ∧ actual.1 = some result ∧ Represents build (.leaf leaf) actual.2 result := by
  cases selected : values[index]? with
  | none =>
      simp only [readForest, selected, run]
      exact ⟨EqualityRawLeafEmpty.zero, .empty, facts, rfl, EqualityRawLeafEmpty.zero_represents state⟩
  | some value =>
      have input := child_input build forest index path state facts.coherent.valid values represented endpoints value selected
      simpa only [readForest, selected] using read_actual path state facts value input

/-- The actual physical intersection needs no later proof-cache allocations for its finite result. -/
theorem intersect_actual (first second : Leaf initial symbols) (left right : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (leftRepresented : Represents build (.leaf first) state left)
    (rightRepresented : Represents build (.leaf second) state right) :
    let actual := run (EqualityRawLeafProduct.intersect left right) state
    Facts actual.2 ∧ Represents build (.leaf (intersect first second)) actual.2 actual.1 := by
  have available := EqualityLeafProjectionRepresentation.available build EqualityRawLeafCompiler.leaves_available
    (.leaf first) state facts left leftRepresented
  have checked := EqualityLeafProjectionActualMeet.raw_intersect_available left right state facts available
  have prepared := EqualityLeafProjectionTargetFold.physical_intersect first second left right state facts leftRepresented rightRepresented
  exact ⟨checked.1, EqualityRawLeafPullback.represented_pullback _ _ _ checked.1 prepared.1 _ checked.2.resident prepared.2.2⟩

/-- The source seeded fold represents its exact finite fold in the actual final runtime cache. -/
theorem fold_actual (seed : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (inputs : List (Leaf initial symbols × Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (seedRepresented : Represents build (.leaf seed) state value)
    (represented : ∀ pair ∈ inputs, Represents build (.leaf pair.1) state pair.2) :
    let actual := run (EqualityLeafProjectionTargetFold.fold value (inputs.map Prod.snd)) state
    Facts actual.2 ∧ Represents build (.leaf ((inputs.map Prod.fst).foldr intersect seed)) actual.2 actual.1 := by
  have seedAvailable := EqualityLeafProjectionRepresentation.available build EqualityRawLeafCompiler.leaves_available
    (.leaf seed) state facts value seedRepresented
  have inputsAvailable : ∀ value ∈ inputs.map Prod.snd, Available state value := by
    intro value member
    obtain ⟨pair, present, rfl⟩ := List.mem_map.mp member
    exact EqualityLeafProjectionRepresentation.available build EqualityRawLeafCompiler.leaves_available
      (.leaf pair.1) state facts pair.2 (represented pair present)
  have checked := EqualityLeafProjectionTargetFold.fold_available value (inputs.map Prod.snd) state facts seedAvailable inputsAvailable
  obtain ⟨after, afterFacts, _, prepared⟩ :=
    EqualityLeafProjectionTargetFold.fold_completed seed value inputs state facts seedRepresented represented
  exact ⟨checked.1, EqualityRawLeafPullback.represented_pullback _ _ after checked.1 afterFacts _ checked.2.resident prepared⟩

/-- Every source class-target fold returns an allocation-free finite representation. -/
theorem intersectList_actual (inputs : List (Leaf initial symbols × Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : ∀ pair ∈ inputs, Represents build (.leaf pair.1) state pair.2) :
    let actual := run (EqualityLeafProjectionTargetFold.intersectList (inputs.map Prod.snd)) state
    Facts actual.2 ∧ Represents build (.leaf
      (EqualityLeafProjectionSchedule.intersectList intersect EqualityRawLeafEmpty.zero (inputs.map Prod.fst))) actual.2 actual.1 := by
  cases inputs with
  | nil => exact ⟨facts, EqualityRawLeafEmpty.zero_represents state⟩
  | cons first rest =>
      exact fold_actual first.1 first.2 rest state facts (represented first (by simp))
        (fun pair member => represented pair (by simp [member]))

end MicroCFTA.EqualityLeafProjectionRuntimeLeaves
