import MicroCFTA.EqualityLeafProjectionEditTransport

/-!
# Parent edit correspondence from strict child occurrences

The actual canonical parent runs first. A finite proof run edits retained
original rows. Resident row normalization then gives the same complete
parent record in the common cache.
-/
namespace MicroCFTA.EqualityLeafProjectionEditParent
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open EqualityLeafProjectionSyntax (Tree Edge Path Admissible atRoot)
open EqualityLeafProjectionCompile (Tag)
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionCompileOrdinary
open EqualityLeafProjectionRepresentation EqualityLeafProjectionWorkers
open EqualityLeafProjectionRequireAvailability EqualityLeafProjectionEditAvailability
open EqualityLeafProjectionEditTransport EqualityLeafProjectionPhysical

/-- Strict child correspondence derives the complete parent result even when
original duplicate and dead rows have disappeared from its canonical cache record. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leafAvailable : LeafAvailable leaf) (leafOrdinary : LeafOrdinary leaf)
    (meet : Leaf → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) (meetAvailable : MeetAvailable meet)
    (join : Leaf → Leaf → Leaf) (edges : List (Edge (Tag Symbol Guard) Leaf))
    (each : ∀ edge ∈ edges, ∀ child ∈ edge.children, Transport leaf meet join child)
    (first : Path × Leaf) (rest : List (Path × Leaf)) (admissible : Admissible (first :: rest) (.node edges))
    (state : State Symbol Guard) (facts : Facts state)
    (value : Value Symbol Guard) (represented : Represents leaf (.node edges) state value) :
    let actual := run (edit meet (first :: rest) value) state
    ∃ after result, Facts after ∧ Grows actual.2 after ∧ actual.1 = some result ∧
      Represents leaf (EqualityLeafProjectionSyntax.edit join (first :: rest) (.node edges)) after result := by
  have noRoot := EqualityLeafProjectionSyntax.admissible_root_none (first :: rest) edges admissible
  obtain ⟨rows, rowsClosed, nodeClosed⟩ := node_decompose leaf edges state facts.coherent.valid value represented
  have rowFacts := compileEdges_available leaf leafAvailable edges state facts
  rw [rowsClosed] at rowFacts
  have rowOrdinary := compileEdges_ordinary leaf leafAvailable leafOrdinary edges state facts
  rw [rowsClosed] at rowOrdinary
  have ordinaryRows := EqualityLeafProjectionParentStep.ordinary_edges rows rowOrdinary
  have inputAvailable := EqualityLeafProjectionRepresentation.available leaf leafAvailable (.node edges) state facts value represented
  have inputOrdinary := compile_ordinary leaf leafAvailable leafOrdinary (.node edges) state facts
  rw [represented] at inputOrdinary
  let actual := run (edit meet (first :: rest) value) state
  have actualChecked := edit_available meet meetAvailable (first :: rest) value state facts inputAvailable
  obtain ⟨result, returned⟩ := edit_returns meet (first :: rest) value inputOrdinary state
  have actualGrowth : Grows state actual.2 := (InternedConstructorTemplates.run_correct _ state facts.coherent.valid).2
  have rowsAvailable : ∀ edge ∈ rows, ChildrenAvailable actual.2 edge.children := by
    intro edge member child present
    exact available_after_run (edit meet (first :: rest) value) state facts.coherent.valid ((rowFacts.2 edge member).2 child present)
  let original := run (editEdges meet (first :: rest) rows) actual.2
  have originalChecked := editEdges_available meet meetAvailable (first :: rest) rows actual.2 actualChecked.1 rowsAvailable
  obtain ⟨outputs, outputReturned⟩ := editEdges_returns meet (first :: rest) rows ordinaryRows actual.2
  have originalGrowth : Grows actual.2 original.2 :=
    (InternedConstructorTemplates.run_correct _ actual.2 actualChecked.1.coherent.valid).2
  have rowsLater := edges_grows leaf edges state original.2 facts.coherent.valid
    (grows_trans actualGrowth originalGrowth) rows rowsClosed
  have originalClosed : run (editEdges meet (first :: rest) rows) original.2 = (some outputs, original.2) := by
    simpa only [outputReturned] using replay (editEdges meet (first :: rest) rows) actual.2 original.2
      actualChecked.1.coherent.valid (grows_refl original.2)
  obtain ⟨after, afterFacts, afterGrowth, changedRows⟩ := closed_edges leaf leafAvailable meet join edges each (first :: rest)
    admissible original.2 originalChecked.1 rows outputs rowsLater originalClosed
  have actualToAfter : Grows actual.2 after := grows_trans originalGrowth afterGrowth
  have readback := EqualityLeafProjectionWorkerReadback.editEdges_readback meet (first :: rest) rows ordinaryRows
    actual.2 after actualChecked.1.coherent.valid afterGrowth
  have outputsSame : outputs = rows.map (rebuild after (editedChild meet (first :: rest) after)) :=
    Option.some.inj (outputReturned.symm.trans readback)
  have outputsResident : ∀ edge ∈ outputs, EdgeResident after edge := by
    intro edge member
    exact edge_grows original.2 after afterGrowth edge ((originalChecked.2 outputs outputReturned) edge member).1
  have rebuiltResident : ∀ edge ∈ rows, EdgeResident after (rebuild after (editedChild meet (first :: rest) after) edge) := by
    intro edge member
    apply outputsResident
    rw [outputsSame]
    exact List.mem_map.mpr ⟨edge, member, rfl⟩
  have normalized := rebuild_readback state after after facts.coherent facts.linked afterFacts.coherent afterFacts.coherent
    rows (fun edge member => (rowFacts.2 edge member).1) (fun _ => true) (editedChild meet (first :: rest) after)
    (editedChild_empty meet (first :: rest) after) rebuiltResident
  simp only [List.filter_eq_self.mpr (fun _ _ => rfl)] at normalized
  rw [nodeClosed] at normalized
  have requestExact : run (makeNode outputs) after = (result, after) := by
    rw [outputsSame, normalized]
    cases value with
    | empty =>
        have resultEmpty : result = .empty := by
          have same : some (.empty : Value Symbol Guard) = some result := by simpa only [edit_empty, run] using returned
          exact (Option.some.inj same).symm
        subst result
        simp [nodeEdges, makeNode, surviving, canonicalEdges, EnumerationBuilderCaches.canonicalIds, run]
    | reference | union | mu => simp only [EqualityLeafProjectionWorkers.Ordinary] at inputOrdinary
    | node entry canonical depth free =>
        exact EqualityLeafProjectionEditClosed.parent_replay meet first rest entry canonical depth free
          (by simpa only [EqualityLeafProjectionWorkers.Ordinary] using inputOrdinary) noRoot
          state after facts.coherent.valid result returned actualToAfter
  refine ⟨after, result, afterFacts, actualToAfter, returned, ?_⟩
  exact node_intro leaf _ after result outputs changedRows requestExact

end MicroCFTA.EqualityLeafProjectionEditParent
