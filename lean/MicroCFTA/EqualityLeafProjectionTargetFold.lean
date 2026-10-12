import MicroCFTA.EqualityLeafProjectionPathExact

/-!
# Actual physical class-target intersection folds

The source seeds the right fold with its first projected operand. Physical
targets already exist before the edit worker runs. Represented leaf builds
replay without allocation, so local physical intersection correspondence
does not insert extra runtime requests.
-/
namespace MicroCFTA.EqualityLeafProjectionTargetFold
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionClosedWorkers (work_grows)
open EqualityRawLeafInventory (Leaf intersect)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- A represented target build is allocation-free before the actual physical intersection. -/
theorem represented_meet_run (leaf : Leaf initial symbols) (left right : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (represented : Represents build (.leaf leaf) state left) :
    run (EqualityRawLeafCompiler.meet leaf right) state = run (EqualityRawLeafProduct.intersect left right) state := by
  have exactTarget : run (build leaf) state = (left, state) := represented
  simp only [EqualityRawLeafCompiler.meet, EqualityLeafProjectionActualMeet.rawMeet, run_bind]
  change run (EqualityRawLeafProduct.intersect (run (build leaf) state).1 right) (run (build leaf) state).2 = _
  rw [exactTarget]

/-- Actual physical leaf intersection gets its complete compiled result after finite proof preparation. -/
theorem physical_intersect (first second : Leaf initial symbols) (left right : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (leftRepresented : Represents build (.leaf first) state left)
    (rightRepresented : Represents build (.leaf second) state right) :
    let actual := run (EqualityRawLeafProduct.intersect left right) state
    let prepared := run (build (intersect first second)) actual.2
    Facts prepared.2 ∧ Grows actual.2 prepared.2 ∧ Represents build (.leaf (intersect first second)) prepared.2 actual.1 := by
  have completed := EqualityRawLeafCompiler.represented_meet first second state right facts rightRepresented
  rw [represented_meet_run first left right state leftRepresented] at completed
  exact completed

/-- Execute the source right fold after its initial projected seed is selected. -/
noncomputable def fold (seed : Value (Fin symbols) ConstraintKey) :
    List (Value (Fin symbols) ConstraintKey) → Work (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey)
  | [] => .pure seed
  | first :: rest => (fold seed rest).bind fun value => EqualityRawLeafProduct.intersect first value

/-- The source uses its first operand as the seed, including its singleton shortcut. -/
noncomputable def intersectList : List (Value (Fin symbols) ConstraintKey) → Work (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey)
  | [] => .pure .empty
  | first :: rest => fold first rest

/-- Closed actual physical target folds derive exact finite-leaf representations in source order. -/
theorem fold_closed (seed : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (inputs : List (Leaf initial symbols × Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (seedRepresented : Represents build (.leaf seed) state value)
    (represented : ∀ pair ∈ inputs, Represents build (.leaf pair.1) state pair.2)
    (result : Value (Fin symbols) ConstraintKey)
    (closed : run (fold value (inputs.map Prod.snd)) state = (result, state)) :
    ∃ after, Facts after ∧ Grows state after ∧
      Represents build (.leaf ((inputs.map Prod.fst).foldr intersect seed)) after result := by
  induction inputs generalizing state result with
  | nil =>
      have same : value = result := congrArg Prod.fst closed
      exact ⟨state, facts, grows_refl state, same ▸ seedRepresented⟩
  | cons first rest ih =>
      obtain ⟨tail, tailClosed, headClosed⟩ := bind_closed _ _ state facts.coherent.valid result closed
      obtain ⟨middle, middleFacts, growth, tailRepresented⟩ :=
        ih state facts seedRepresented (fun pair member => represented pair (by simp [member])) tail tailClosed
      have firstRepresented := EqualityLeafProjectionRepresentation.grows build (.leaf first.1) state middle
        facts.coherent.valid growth first.2 (represented first (by simp))
      have headReplay : run (EqualityRawLeafProduct.intersect first.2 tail) middle = (result, middle) :=
        work_grows _ state middle facts.coherent.valid result headClosed growth
      have completed := physical_intersect first.1 ((rest.map Prod.fst).foldr intersect seed) first.2 tail
        middle middleFacts firstRepresented tailRepresented
      rw [headReplay] at completed
      exact ⟨_, completed.1, grows_trans growth completed.2.1, completed.2.2⟩

/-- The actual seeded fold preserves complete source payloads through every operand. -/
theorem fold_available (seed : Value (Fin symbols) ConstraintKey) (values : List (Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (seedAvailable : Available state seed)
    (available : ∀ value ∈ values, Available state value) :
    Facts (run (fold seed values) state).2 ∧ Available (run (fold seed values) state).2 (run (fold seed values) state).1 := by
  induction values with
  | nil => exact ⟨facts, seedAvailable⟩
  | cons first rest ih =>
      have tail := ih (fun value member => available value (by simp [member]))
      have head := available_after_run (fold seed rest) state facts.coherent.valid (available first (by simp))
      simp only [fold, run_bind]
      exact EqualityLeafProjectionActualMeet.raw_intersect_available first _ _ tail.1 head

/-- Execute the actual physical seed fold first, then derive the exact finite abstract fold record. -/
theorem fold_completed (seed : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (inputs : List (Leaf initial symbols × Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (seedRepresented : Represents build (.leaf seed) state value)
    (represented : ∀ pair ∈ inputs, Represents build (.leaf pair.1) state pair.2) :
    let actual := run (fold value (inputs.map Prod.snd)) state
    ∃ after, Facts after ∧ Grows actual.2 after ∧
      Represents build (.leaf ((inputs.map Prod.fst).foldr intersect seed)) after actual.1 := by
  let actual := run (fold value (inputs.map Prod.snd)) state
  have seedAvailable := EqualityLeafProjectionRepresentation.available build EqualityRawLeafCompiler.leaves_available
    (.leaf seed) state facts value seedRepresented
  have available : ∀ value ∈ inputs.map Prod.snd, Available state value := by
    intro value member
    obtain ⟨pair, present, rfl⟩ := List.mem_map.mp member
    exact EqualityLeafProjectionRepresentation.available build EqualityRawLeafCompiler.leaves_available
      (.leaf pair.1) state facts pair.2 (represented pair present)
  have actualFacts := fold_available value (inputs.map Prod.snd) state facts seedAvailable available
  have growth : Grows state actual.2 := (InternedConstructorTemplates.run_correct _ state facts.coherent.valid).2
  have seedLater := EqualityLeafProjectionRepresentation.grows build (.leaf seed) state actual.2
    facts.coherent.valid growth value seedRepresented
  have inputsLater : ∀ pair ∈ inputs, Represents build (.leaf pair.1) actual.2 pair.2 :=
    fun pair member => EqualityLeafProjectionRepresentation.grows build (.leaf pair.1) state actual.2
      facts.coherent.valid growth pair.2 (represented pair member)
  exact fold_closed seed value inputs actual.2 actualFacts.1 seedLater inputsLater actual.1
    (replay (fold value (inputs.map Prod.snd)) state actual.2 facts.coherent.valid (grows_refl actual.2))

/-- The complete source target fold represents exactly its first-seeded finite counterpart. -/
theorem intersectList_completed (inputs : List (Leaf initial symbols × Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : ∀ pair ∈ inputs, Represents build (.leaf pair.1) state pair.2) :
    let actual := run (intersectList (inputs.map Prod.snd)) state
    ∃ after, Facts after ∧ Grows actual.2 after ∧
      Represents build (.leaf (EqualityLeafProjectionSchedule.intersectList intersect EqualityRawLeafEmpty.zero
        (inputs.map Prod.fst))) after actual.1 := by
  cases inputs with
  | nil => exact ⟨state, facts, grows_refl state, EqualityRawLeafEmpty.zero_represents state⟩
  | cons first rest =>
      exact fold_completed first.1 first.2 rest state facts (represented first (by simp))
        (fun pair member => represented pair (by simp [member]))

end MicroCFTA.EqualityLeafProjectionTargetFold
