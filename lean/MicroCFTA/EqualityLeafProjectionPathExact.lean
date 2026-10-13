import MicroCFTA.EqualityLeafProjectionPathTransport

/-!
# Complete represented leaf endpoints from actual path projection

The source path worker runs on canonical physical rows. Closed component
traces derive represented finite leaf operands for the actual union. The
result needs no caller-supplied read law or globally closed finite cache.
-/
namespace MicroCFTA.EqualityLeafProjectionPathExact
open InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionPathWorker EqualityLeafProjectionPathInputs EqualityLeafProjectionPathTransport
open EqualityLeafProjectionClosedWorkers (optional_bind_closed work_grows)
open EqualityRawLeafInventory (Leaf)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)
open EqualityLeafProjectionSyntax (Path LeafAt)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Every completed source projection at an original leaf endpoint has an exact finite representation. -/
theorem read_transport (path : Path) : Transport initial symbols path := by
  induction path with
  | nil =>
      intro state facts value input result closed
      obtain ⟨tree, endpoint, represented⟩ := input
      have same : value = result := Option.some.inj (congrArg Prod.fst closed)
      subst result
      cases tree with
      | empty =>
          have empty : value = .empty := (congrArg (fun result : Value (Fin symbols) ConstraintKey × State (Fin symbols) ConstraintKey => result.1) represented).symm
          subst value
          exact ⟨state, EqualityRawLeafEmpty.zero, facts, grows_refl state, EqualityRawLeafEmpty.zero_represents state⟩
      | leaf leaf => exact ⟨state, leaf, facts, grows_refl state, represented⟩
      | node edges => cases endpoint
  | cons index path ih =>
      intro state facts value input result closed
      obtain ⟨tree, endpoint, represented⟩ := input
      cases tree with
      | empty =>
          have empty : value = .empty := (congrArg (fun result : Value (Fin symbols) ConstraintKey × State (Fin symbols) ConstraintKey => result.1) represented).symm
          subst value
          rw [EqualityRawLeafEmpty.read_empty] at closed
          have same : result = .empty := (Option.some.inj (congrArg Prod.fst closed)).symm
          subst result
          exact ⟨state, EqualityRawLeafEmpty.zero, facts, grows_refl state, EqualityRawLeafEmpty.zero_represents state⟩
      | leaf leaf =>
          rw [EqualityRawLeafEmpty.read_represented leaf state facts value represented index path] at closed
          have same : result = .empty := (Option.some.inj (congrArg Prod.fst closed)).symm
          subst result
          exact ⟨state, EqualityRawLeafEmpty.zero, facts, grows_refl state, EqualityRawLeafEmpty.zero_represents state⟩
      | node original =>
          have inputs := node_inputs build EqualityRawLeafCompiler.leaves_available original index path state facts value represented endpoint
          have ordinary := EqualityLeafProjectionCompileOrdinary.compile_ordinary build EqualityRawLeafCompiler.leaves_available
            EqualityRawLeafCompiler.leaves_ordinary (.node original) state facts
          rw [represented] at ordinary
          cases value with
          | empty =>
              rw [EqualityRawLeafEmpty.read_empty] at closed
              have same : result = .empty := (Option.some.inj (congrArg Prod.fst closed)).symm
              subst result
              exact ⟨state, EqualityRawLeafEmpty.zero, facts, grows_refl state, EqualityRawLeafEmpty.zero_represents state⟩
          | reference | union | mu => cases ordinary
          | node entry edges depth free =>
              obtain ⟨values, rowsClosed, later⟩ := optional_bind_closed _ _ state facts.coherent.valid result closed
              obtain ⟨actual, unionClosed, finalClosed⟩ := bind_closed _ _ state facts.coherent.valid (some result) later
              have same : actual = result := Option.some.inj (congrArg Prod.fst finalClosed)
              subst actual
              obtain ⟨middle, pairs, middleFacts, growth, order, projected⟩ :=
                rows_transport path ih index edges state facts inputs values rowsClosed
              have unionReplay : run (makeUnion (pairs.map Prod.snd)) middle = (result, middle) := by
                have fields := EqualityRawLeafUnion.operand_fields pairs middle middleFacts projected
                rw [← EqualityOrdinaryUnionSource.union_run (pairs.map Prod.snd) middle middleFacts.coherent middleFacts.linked
                  (fun value member => (fields value member).1)
                  (fun value member => (fields value member).2.2.1)
                  (fun value member => (fields value member).2.1)]
                rw [order]
                exact work_grows (EqualityOrdinaryUnionSource.sourceUnion values) state middle facts.coherent.valid result unionClosed growth
              have completed := EqualityRawLeafUnion.union_completed pairs middle middleFacts projected
              rw [unionReplay] at completed
              exact ⟨_, EqualityRawLeafUnion.union (pairs.map Prod.fst), completed.1,
                grows_trans growth completed.2.1, completed.2.2⟩

/-- Run an actual represented endpoint read and derive its later complete finite leaf representation. -/
theorem read_completed (path : Path) (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (value : Value (Fin symbols) ConstraintKey) (input : Input (build (initial := initial)) path state value) :
    let actual := run (read path value) state
    ∃ after, ∃ leaf : Leaf initial symbols, ∃ result,
      Facts after ∧ Grows actual.2 after ∧ actual.1 = some result ∧ Represents build (.leaf leaf) after result := by
  obtain ⟨tree, endpoint, represented⟩ := input
  have available := EqualityLeafProjectionRepresentation.available build EqualityRawLeafCompiler.leaves_available tree state facts value represented
  have ordinary := EqualityLeafProjectionCompileOrdinary.compile_ordinary build EqualityRawLeafCompiler.leaves_available
    EqualityRawLeafCompiler.leaves_ordinary tree state facts
  rw [represented] at ordinary
  obtain ⟨result, returned⟩ := read_returns path value ordinary state
  have checked := read_available path value state facts available
  let actual := run (read path value) state
  have growth : Grows state actual.2 := (InternedConstructorTemplates.run_correct _ state facts.coherent.valid).2
  have closed : run (read path value) actual.2 = (some result, actual.2) := by
    simpa only [returned] using replay (read path value) state actual.2 facts.coherent.valid (grows_refl actual.2)
  have laterInput := input_grows build path state actual.2 facts.coherent.valid growth value ⟨tree, endpoint, represented⟩
  obtain ⟨after, leaf, afterFacts, later, represented⟩ := read_transport path actual.2 checked.1 value laterInput result closed
  exact ⟨after, leaf, result, afterFacts, later, returned, represented⟩

/-- Compiled original leaf endpoints supply every premise of the actual source read theorem. -/
theorem compiled_raw_read
    (tree : EqualityLeafProjectionSyntax.Tree
      (EqualityLeafProjectionCompile.Tag (Fin symbols) ConstraintKey) (Leaf initial symbols))
    (path : Path) (endpoint : LeafAt path tree) (state : State (Fin symbols) ConstraintKey) (facts : Facts state) :
    let compiled := run (EqualityLeafProjectionCompile.compile build tree) state
    let actual := run (read path compiled.1) compiled.2
    ∃ after, ∃ leaf : Leaf initial symbols, ∃ result,
      Facts after ∧ Grows actual.2 after ∧ actual.1 = some result ∧ Represents build (.leaf leaf) after result := by
  let compiled := run (EqualityLeafProjectionCompile.compile build tree) state
  have compiledFacts := compile_available build EqualityRawLeafCompiler.leaves_available tree state facts
  exact read_completed path compiled.2 compiledFacts.1 compiled.1
    ⟨tree, endpoint, completed build tree state facts.coherent.valid⟩

/-- Actual nonempty forest paths derive represented finite leaf results from original endpoints. -/
theorem forest_read_completed
    (forest : List (EqualityLeafProjectionSyntax.Tree
      (EqualityLeafProjectionCompile.Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (index : Nat) (path : Path) (endpoints : EqualityLeafProjectionSyntax.ChildAt index path forest)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (values : List (Value (Fin symbols) ConstraintKey))
    (represented : RepresentsForest build forest state values) :
    let actual := run (readForest (index :: path) values) state
    ∃ after, ∃ leaf : Leaf initial symbols, ∃ result,
      Facts after ∧ Grows actual.2 after ∧ actual.1 = some result ∧ Represents build (.leaf leaf) after result := by
  cases selected : values[index]? with
  | none =>
      simp only [readForest, selected, run]
      exact ⟨state, EqualityRawLeafEmpty.zero, .empty, facts, grows_refl state, rfl, EqualityRawLeafEmpty.zero_represents state⟩
  | some value =>
      have input := child_input build forest index path state facts.coherent.valid values represented endpoints value selected
      simpa only [readForest, selected] using read_completed path state facts value input

end MicroCFTA.EqualityLeafProjectionPathExact
