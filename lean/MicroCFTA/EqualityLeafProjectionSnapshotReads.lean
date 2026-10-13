import MicroCFTA.EqualityLeafProjectionRuntimeLeaves

/-!
# Ordered endpoint reads from an unchanged class snapshot

Every read uses the same original child forest. Only the runtime cache
advances. Finite leaf witnesses are retained in each actual output cache.
-/
namespace MicroCFTA.EqualityLeafProjectionSnapshotReads
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionWorkers (bindOptional)
open EqualityLeafProjectionSyntax (Path Tree Endpoints)
open EqualityLeafProjectionCompile (Tag)
open EqualityRawLeafInventory (Leaf)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Read class paths in their supplied source order from one physical snapshot. -/
noncomputable def readMany (paths : List Path) (snapshot : List (Value (Fin symbols) ConstraintKey)) :
    Work (Fin symbols) ConstraintKey (Option (List (Value (Fin symbols) ConstraintKey))) :=
  match paths with
  | [] => .pure (some [])
  | path :: rest => bindOptional (EqualityLeafProjectionPathWorker.readForest path snapshot) fun value =>
      bindOptional (readMany rest snapshot) fun values => .pure (some (value :: values))

/-- Each source snapshot read returns finite operands in the actual final runtime cache. -/
theorem readMany_actual (paths : List Path)
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (proper : ∀ path ∈ paths, path ≠ []) (endpoints : Endpoints paths forest)
    (snapshot : List (Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : RepresentsForest build forest state snapshot) :
    let actual := run (readMany paths snapshot) state
    ∃ inputs : List (Leaf initial symbols × Value (Fin symbols) ConstraintKey),
      Facts actual.2 ∧ actual.1 = some (inputs.map Prod.snd) ∧
      ∀ pair ∈ inputs, Represents build (.leaf pair.1) actual.2 pair.2 := by
  induction paths generalizing state with
  | nil => exact ⟨[], facts, rfl, by simp⟩
  | cons path rest ih =>
      cases path with
      | nil => exact False.elim (proper [] (by simp) rfl)
      | cons index path =>
          let head := run (EqualityLeafProjectionPathWorker.readForest (index :: path) snapshot) state
          obtain ⟨leaf, value, headFacts, headReturned, headRepresented⟩ :=
            EqualityLeafProjectionRuntimeLeaves.forest_read_actual forest index path (endpoints (index :: path) (by simp))
              state facts snapshot represented
          have headGrowth : Grows state head.2 := (InternedConstructorTemplates.run_correct _ state facts.coherent.valid).2
          have forestLater := forest_grows build forest state head.2 facts.coherent.valid headGrowth snapshot represented
          obtain ⟨tail, tailFacts, tailReturned, tailRepresented⟩ := ih
            (fun path member => proper path (by simp [member]))
            (fun path member => endpoints path (by simp [member])) head.2 headFacts forestLater
          let result := run (readMany rest snapshot) head.2
          have tailGrowth : Grows head.2 result.2 := (InternedConstructorTemplates.run_correct _ head.2 headFacts.coherent.valid).2
          have leafLater := EqualityLeafProjectionRepresentation.grows build (.leaf leaf) head.2 result.2
            headFacts.coherent.valid tailGrowth value headRepresented
          dsimp only [head] at tailReturned
          refine ⟨(leaf, value) :: tail, ?_⟩
          simp only [readMany, bindOptional, run_bind, headReturned, tailReturned, run, List.map_cons]
          refine ⟨tailFacts, trivial, ?_⟩
          intro pair member
          rcases List.mem_cons.mp member with same | member
          · subst pair
            exact leafLater
          · exact tailRepresented pair member

end MicroCFTA.EqualityLeafProjectionSnapshotReads
