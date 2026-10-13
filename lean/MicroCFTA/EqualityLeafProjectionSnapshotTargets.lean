import MicroCFTA.EqualityLeafProjectionSnapshotReads

/-!
# Complete physical targets from one equality-class snapshot

Each path target intersects all other class projections. The source keeps
the first projected operand as the right-fold seed. Every target reads the
same forest before any simultaneous edit starts.
-/
namespace MicroCFTA.EqualityLeafProjectionSnapshotTargets
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionWorkers (bindOptional)
open EqualityLeafProjectionSyntax (Path Tree Endpoints)
open EqualityLeafProjectionCompile (Tag)
open EqualityRawLeafInventory (Leaf)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Build the retained physical target for one source class position. -/
noncomputable def target (paths : List Path) (path : Path) (snapshot : List (Value (Fin symbols) ConstraintKey)) :
    Work (Fin symbols) ConstraintKey (Option (Value (Fin symbols) ConstraintKey)) :=
  bindOptional (EqualityLeafProjectionSnapshotReads.readMany (paths.filter (· != path)) snapshot) fun values =>
    (EqualityLeafProjectionTargetFold.intersectList values).bind fun value => .pure (some value)

/-- The source target is represented in its own actual runtime output cache. -/
theorem target_actual (paths : List Path) (path : Path)
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (proper : ∀ path ∈ paths, path ≠ []) (endpoints : Endpoints paths forest)
    (snapshot : List (Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : RepresentsForest build forest state snapshot) :
    let actual := run (target paths path snapshot) state
    ∃ leaf : Leaf initial symbols, ∃ result,
      Facts actual.2 ∧ actual.1 = some result ∧ Represents build (.leaf leaf) actual.2 result := by
  let projected := run (EqualityLeafProjectionSnapshotReads.readMany (paths.filter (· != path)) snapshot) state
  obtain ⟨inputs, projectedFacts, returned, inputsRepresented⟩ :=
    EqualityLeafProjectionSnapshotReads.readMany_actual (paths.filter (· != path)) forest
      (fun path member => proper path (List.mem_filter.mp member).1)
      (fun path member => endpoints path (List.mem_filter.mp member).1) snapshot state facts represented
  have folded := EqualityLeafProjectionRuntimeLeaves.intersectList_actual inputs projected.2 projectedFacts inputsRepresented
  refine ⟨EqualityLeafProjectionSchedule.intersectList EqualityRawLeafInventory.intersect EqualityRawLeafEmpty.zero
    (inputs.map Prod.fst), (run (EqualityLeafProjectionTargetFold.intersectList (inputs.map Prod.snd)) projected.2).1, ?_⟩
  simp only [target, bindOptional, run_bind, returned, run]
  exact ⟨folded.1, rfl, folded.2⟩

/-- Construct each class closure in order while retaining its original path. -/
noncomputable def targets (paths : List Path) (requested : List Path)
    (snapshot : List (Value (Fin symbols) ConstraintKey)) :
    Work (Fin symbols) ConstraintKey (Option (List (Path × Value (Fin symbols) ConstraintKey))) :=
  match requested with
  | [] => .pure (some [])
  | path :: rest => bindOptional (target paths path snapshot) fun value =>
      bindOptional (targets paths rest snapshot) fun values => .pure (some ((path, value) :: values))

/-- All physical class closures have finite witnesses before simultaneous editing begins. -/
theorem targets_actual (paths requested : List Path)
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (proper : ∀ path ∈ paths, path ≠ []) (endpoints : Endpoints paths forest)
    (snapshot : List (Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : RepresentsForest build forest state snapshot) :
    let actual := run (targets paths requested snapshot) state
    ∃ edits : List (Path × (Leaf initial symbols × Value (Fin symbols) ConstraintKey)),
      Facts actual.2 ∧ edits.map Prod.fst = requested ∧
      actual.1 = some (EqualityLeafProjectionEditRelabel.targets Prod.snd edits) ∧
      ∀ path pair, (path, pair) ∈ edits → Represents build (.leaf pair.1) actual.2 pair.2 := by
  induction requested generalizing state with
  | nil => exact ⟨[], facts, rfl, rfl, by simp⟩
  | cons path rest ih =>
      let head := run (target paths path snapshot) state
      obtain ⟨leaf, value, headFacts, headReturned, headRepresented⟩ :=
        target_actual paths path forest proper endpoints snapshot state facts represented
      have headGrowth : Grows state head.2 := (InternedConstructorTemplates.run_correct _ state facts.coherent.valid).2
      have forestLater := forest_grows build forest state head.2 facts.coherent.valid headGrowth snapshot represented
      obtain ⟨tail, tailFacts, tailPaths, tailReturned, tailRepresented⟩ := ih head.2 headFacts forestLater
      let result := run (targets paths rest snapshot) head.2
      have tailGrowth : Grows head.2 result.2 := (InternedConstructorTemplates.run_correct _ head.2 headFacts.coherent.valid).2
      have leafLater := EqualityLeafProjectionRepresentation.grows build (.leaf leaf) head.2 result.2
        headFacts.coherent.valid tailGrowth value headRepresented
      dsimp only [head] at tailReturned
      refine ⟨(path, (leaf, value)) :: tail, ?_⟩
      simp only [targets, bindOptional, run_bind, headReturned, tailReturned, run,
        EqualityLeafProjectionEditRelabel.targets, List.map_cons]
      refine ⟨tailFacts, congrArg (path :: ·) tailPaths, trivial, ?_⟩
      intro selected pair member
      rcases List.mem_cons.mp member with same | member
      · have pairSame := (Prod.mk.inj same).2
        cases pairSame
        exact leafLater
      · exact tailRepresented selected pair member

end MicroCFTA.EqualityLeafProjectionSnapshotTargets
