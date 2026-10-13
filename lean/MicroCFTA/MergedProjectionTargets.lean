import MicroCFTA.MergedRawLeafSource
import MicroCFTA.EqualityLeafProjectionSnapshotTargets

/-!
# Physical merged targets from a projected-leaf snapshot

Each peer projection passes through the physical merge worker before
the seeded intersection fold. Every next operation uses the preceding
runtime cache. Group iteration order remains an explicit source input.
-/
namespace MicroCFTA.MergedProjectionTargets
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionWorkers (bindOptional)
open EqualityLeafProjectionSyntax (Path Tree Endpoints)
open EqualityLeafProjectionCompile (Tag)
open EqualityRawLeafInventory (Leaf)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- The source group order includes each symbol read from the actual value. -/
def CompleteOrder (order : Value (Fin symbols) ConstraintKey → List (Fin symbols)) : Prop :=
  ∀ value, MergedRawLeafSource.Complete (order value) value

/-- Merge the projected operands in their retained source order. -/
noncomputable def mergeMany (order : Value (Fin symbols) ConstraintKey → List (Fin symbols)) :
    List (Value (Fin symbols) ConstraintKey) →
      Work (Fin symbols) ConstraintKey (List (Value (Fin symbols) ConstraintKey))
  | [] => .pure []
  | value :: rest => (MergedRawLeafSource.worker (order value) value).bind fun merged =>
      (mergeMany order rest).bind fun others => .pure (merged :: others)

/-- Every merged operand has its exact representation in the final runtime cache. -/
theorem mergeMany_actual (order : Value (Fin symbols) ConstraintKey → List (Fin symbols))
    (complete : CompleteOrder order)
    (inputs : List (Leaf initial symbols × Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : ∀ pair ∈ inputs, Represents build (.leaf pair.1) state pair.2) :
    let actual := run (mergeMany order (inputs.map Prod.snd)) state
    ∃ outputs : List (Leaf initial symbols × Value (Fin symbols) ConstraintKey),
      Facts actual.2 ∧ actual.1 = outputs.map Prod.snd ∧
      outputs.map Prod.fst = inputs.map (fun pair => MergedRawLeaves.merge pair.1) ∧
      ∀ pair ∈ outputs, Represents build (.leaf pair.1) actual.2 pair.2 := by
  induction inputs generalizing state with
  | nil => exact ⟨[], facts, rfl, rfl, by simp⟩
  | cons first rest ih =>
      let head := run (MergedRawLeafSource.worker (order first.2) first.2) state
      have checked := MergedRawLeafSource.worker_actual first.1 first.2 state facts
        (represented first (by simp)) (order first.2) (complete first.2)
      have growth : Grows state head.2 := (run_correct _ state facts.coherent.valid).2
      have restRepresented : ∀ pair ∈ rest, Represents build (.leaf pair.1) head.2 pair.2 := by
        intro pair member
        exact EqualityLeafProjectionRepresentation.grows build (.leaf pair.1) state head.2
          facts.coherent.valid growth pair.2 (represented pair (by simp [member]))
      obtain ⟨outputs, afterFacts, returned, leaves, outputRepresented⟩ := ih head.2 checked.1 restRepresented
      let tail := run (mergeMany order (rest.map Prod.snd)) head.2
      have tailGrowth : Grows head.2 tail.2 := (run_correct _ head.2 checked.1.coherent.valid).2
      have headRepresented := EqualityLeafProjectionRepresentation.grows build (.leaf (MergedRawLeaves.merge first.1))
        head.2 tail.2 checked.1.coherent.valid tailGrowth head.1 checked.2
      refine ⟨(MergedRawLeaves.merge first.1, head.1) :: outputs, ?_⟩
      simp only [List.map_cons, mergeMany, run_bind, run]
      change Facts tail.2 ∧ head.1 :: tail.1 = head.1 :: outputs.map Prod.snd ∧
        MergedRawLeaves.merge first.1 :: outputs.map Prod.fst =
          MergedRawLeaves.merge first.1 :: rest.map (fun pair => MergedRawLeaves.merge pair.1) ∧ _
      refine ⟨afterFacts, congrArg (head.1 :: ·) returned, congrArg (MergedRawLeaves.merge first.1 :: ·) leaves, ?_⟩
      intro pair member
      rcases List.mem_cons.mp member with rfl | member
      · exact headRepresented
      · exact outputRepresented pair member

/-- Read each other path, merge each physical projection, then apply the original seeded fold. -/
noncomputable def target (order : Value (Fin symbols) ConstraintKey → List (Fin symbols))
    (paths : List Path) (path : Path) (snapshot : List (Value (Fin symbols) ConstraintKey)) :
    Work (Fin symbols) ConstraintKey (Option (Value (Fin symbols) ConstraintKey)) :=
  bindOptional (EqualityLeafProjectionSnapshotReads.readMany (paths.filter (· != path)) snapshot) fun values =>
    (mergeMany order values).bind fun merged =>
      (EqualityLeafProjectionTargetFold.intersectList merged).bind fun value => .pure (some value)

/-- A merged physical target is represented in its own actual runtime output cache. -/
theorem target_actual (order : Value (Fin symbols) ConstraintKey → List (Fin symbols))
    (complete : CompleteOrder order) (paths : List Path) (path : Path)
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (proper : ∀ path ∈ paths, path ≠ []) (endpoints : Endpoints paths forest)
    (snapshot : List (Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : RepresentsForest build forest state snapshot) :
    let actual := run (target order paths path snapshot) state
    ∃ leaf : Leaf initial symbols, ∃ result,
      Facts actual.2 ∧ actual.1 = some result ∧ Represents build (.leaf leaf) actual.2 result := by
  let projected := run (EqualityLeafProjectionSnapshotReads.readMany (paths.filter (· != path)) snapshot) state
  obtain ⟨inputs, projectedFacts, returned, inputsRepresented⟩ :=
    EqualityLeafProjectionSnapshotReads.readMany_actual (paths.filter (· != path)) forest
      (fun path member => proper path (List.mem_filter.mp member).1)
      (fun path member => endpoints path (List.mem_filter.mp member).1) snapshot state facts represented
  obtain ⟨outputs, mergedFacts, mergedReturned, _, mergedRepresented⟩ :=
    mergeMany_actual order complete inputs projected.2 projectedFacts inputsRepresented
  let merged := run (mergeMany order (inputs.map Prod.snd)) projected.2
  have folded := EqualityLeafProjectionRuntimeLeaves.intersectList_actual outputs merged.2 mergedFacts mergedRepresented
  refine ⟨EqualityLeafProjectionSchedule.intersectList EqualityRawLeafInventory.intersect EqualityRawLeafEmpty.zero
    (outputs.map Prod.fst), (run (EqualityLeafProjectionTargetFold.intersectList (outputs.map Prod.snd)) merged.2).1, ?_⟩
  dsimp only [projected] at mergedReturned
  simp only [target, bindOptional, run_bind, returned, mergedReturned, run]
  exact ⟨folded.1, rfl, folded.2⟩

/-- Construct each class closure in order while retaining its original path. -/
noncomputable def targets (order : Value (Fin symbols) ConstraintKey → List (Fin symbols)) (paths : List Path) (requested : List Path)
    (snapshot : List (Value (Fin symbols) ConstraintKey)) :
    Work (Fin symbols) ConstraintKey (Option (List (Path × Value (Fin symbols) ConstraintKey))) :=
  match requested with
  | [] => .pure (some [])
  | path :: rest => bindOptional (target order paths path snapshot) fun value =>
      bindOptional (targets order paths rest snapshot) fun values => .pure (some ((path, value) :: values))

/-- All physical class closures have finite witnesses before simultaneous editing begins. -/
theorem targets_actual (order : Value (Fin symbols) ConstraintKey → List (Fin symbols))
    (complete : CompleteOrder order) (paths requested : List Path)
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (proper : ∀ path ∈ paths, path ≠ []) (endpoints : Endpoints paths forest)
    (snapshot : List (Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : RepresentsForest build forest state snapshot) :
    let actual := run (targets order paths requested snapshot) state
    ∃ edits : List (Path × (Leaf initial symbols × Value (Fin symbols) ConstraintKey)),
      Facts actual.2 ∧ edits.map Prod.fst = requested ∧
      actual.1 = some (EqualityLeafProjectionEditRelabel.targets Prod.snd edits) ∧
      ∀ path pair, (path, pair) ∈ edits → Represents build (.leaf pair.1) actual.2 pair.2 := by
  induction requested generalizing state with
  | nil => exact ⟨[], facts, rfl, rfl, by simp⟩
  | cons path rest ih =>
      let head := run (target order paths path snapshot) state
      obtain ⟨leaf, value, headFacts, headReturned, headRepresented⟩ :=
        target_actual order complete paths path forest proper endpoints snapshot state facts represented
      have headGrowth : Grows state head.2 := (InternedConstructorTemplates.run_correct _ state facts.coherent.valid).2
      have forestLater := forest_grows build forest state head.2 facts.coherent.valid headGrowth snapshot represented
      obtain ⟨tail, tailFacts, tailPaths, tailReturned, tailRepresented⟩ := ih head.2 headFacts forestLater
      let result := run (targets order paths rest snapshot) head.2
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

end MicroCFTA.MergedProjectionTargets
