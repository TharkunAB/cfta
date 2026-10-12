import MicroCFTA.EqualityLeafProjectionRequireTransport

/-!
# Parent requirement correspondence from strict child occurrences

The source parent runs first. A finite proof run then evaluates requirements
on retained original rows. Strict child correspondence represents those row
results. Canonical row normalization recovers the already returned parent
record in the final complete cache.
-/
namespace MicroCFTA.EqualityLeafProjectionRequireParent
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open EqualityLeafProjectionSyntax (Tree Edge Path fits)
open EqualityLeafProjectionCompile (Tag)
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionCompileOrdinary
open EqualityLeafProjectionRepresentation EqualityLeafProjectionWorkers
open EqualityLeafProjectionRequireAvailability EqualityLeafProjectionClosedWorkers
open EqualityLeafProjectionRequireTransport EqualityLeafProjectionPhysical

/-- Original selected rows and canonical selected rows rebuild identically when
the actual row worker has made every selected output resident. -/
theorem selected_normalization [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (rows : List (EdgeValue Symbol Guard))
    (before after : State Symbol Guard) (beforeFacts : Facts before) (afterFacts : Facts after)
    (growth : Grows before after) (resident : ∀ edge ∈ rows, EdgeResident before edge)
    (outputs : ∀ edge ∈ rows.filter (fun edge => fits paths edge.children.length),
      EdgeResident after (rebuild after (requiredChild paths after) edge)) :
    makeNode ((rows.filter (fun edge => fits paths edge.children.length)).map (rebuild after (requiredChild paths after))) =
      makeNode (((nodeEdges (run (makeNode rows) before).1).filter (fun edge => fits paths edge.children.length)).map
        (rebuild after (requiredChild paths after))) := by
  let select := fun edge : EdgeValue Symbol Guard => fits paths edge.children.length
  let changed := fun edge => if select edge then rebuild after (requiredChild paths after) edge else edge
  have changedResident : ∀ edge ∈ rows, EdgeResident after (changed edge) := by
    intro edge member
    dsimp only [changed]
    split
    · exact outputs edge (List.mem_filter.mpr ⟨member, ‹_›⟩)
    · exact edge_grows before after growth edge (resident edge member)
  have preservesDead : ∀ edge ∈ rows, dead edge = true → dead (changed edge) = true := by
    intro edge _ isDead
    dsimp only [changed]
    split
    · exact rebuild_dead after afterFacts.coherent (requiredChild paths after) (requiredChild_empty paths after) edge isDead
    · exact isDead
  have normalized := mapped_readback before after beforeFacts.coherent beforeFacts.linked afterFacts.coherent
    rows resident select changed changedResident preservesDead
  have exactMap : ∀ edges : List (EdgeValue Symbol Guard), (edges.filter select).map changed =
      (edges.filter select).map (rebuild after (requiredChild paths after)) := by
    intro edges
    apply List.map_congr_left
    intro edge member
    exact ite_eq_left (List.mem_filter.mp member).2
  rw [exactMap, exactMap] at normalized
  exact normalized

/-- Strict child occurrence correspondence proves the complete actual parent
requirement result, including dead rows and an original empty canonical parent. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leafAvailable : LeafAvailable leaf) (leafOrdinary : LeafOrdinary leaf)
    (edges : List (Edge (Tag Symbol Guard) Leaf))
    (each : ∀ edge ∈ edges, ∀ child ∈ edge.children, Transport leaf child)
    (paths : List Path) (proper : fits paths 0 = false) (state : State Symbol Guard) (facts : Facts state)
    (value : Value Symbol Guard) (represented : Represents leaf (.node edges) state value) :
    let actual := run (require paths value) state
    ∃ after result, Facts after ∧ Grows actual.2 after ∧ actual.1 = some result ∧
      Represents leaf (EqualityLeafProjectionSyntax.require paths (.node edges)) after result := by
  obtain ⟨rows, rowsClosed, nodeClosed⟩ := node_decompose leaf edges state facts.coherent.valid value represented
  have rowFacts := compileEdges_available leaf leafAvailable edges state facts
  rw [rowsClosed] at rowFacts
  have rowOrdinary := compileEdges_ordinary leaf leafAvailable leafOrdinary edges state facts
  rw [rowsClosed] at rowOrdinary
  have ordinaryRows := EqualityLeafProjectionParentStep.ordinary_edges rows rowOrdinary
  have inputAvailable := EqualityLeafProjectionRepresentation.available leaf leafAvailable (.node edges) state facts value represented
  have inputOrdinary := compile_ordinary leaf leafAvailable leafOrdinary (.node edges) state facts
  rw [represented] at inputOrdinary
  let actual := run (require paths value) state
  have actualChecked := require_available paths value state facts inputAvailable
  obtain ⟨result, returned⟩ := require_returns paths value inputOrdinary state
  have actualGrowth : Grows state actual.2 := (InternedConstructorTemplates.run_correct _ state facts.coherent.valid).2
  have rowsAvailable : ∀ edge ∈ rows, ChildrenAvailable actual.2 edge.children := by
    intro edge member child present
    exact available_after_run (require paths value) state facts.coherent.valid ((rowFacts.2 edge member).2 child present)
  let original := run (requireEdges paths rows) actual.2
  have originalChecked := requireEdges_available paths rows actual.2 actualChecked.1 rowsAvailable
  obtain ⟨outputs, outputReturned⟩ := requireEdges_returns paths rows ordinaryRows actual.2
  have originalGrowth : Grows actual.2 original.2 :=
    (InternedConstructorTemplates.run_correct _ actual.2 actualChecked.1.coherent.valid).2
  have rowsLater := edges_grows leaf edges state original.2 facts.coherent.valid
    (grows_trans actualGrowth originalGrowth) rows rowsClosed
  have originalClosed : run (requireEdges paths rows) original.2 = (some outputs, original.2) := by
    simpa only [outputReturned] using replay (requireEdges paths rows) actual.2 original.2
      actualChecked.1.coherent.valid (grows_refl original.2)
  obtain ⟨after, afterFacts, afterGrowth, changedRows⟩ := closed_edges leaf leafAvailable edges each paths
    original.2 originalChecked.1 rows outputs rowsLater originalClosed
  have totalGrowth : Grows state after := grows_trans actualGrowth (grows_trans originalGrowth afterGrowth)
  have actualToAfter : Grows actual.2 after := grows_trans originalGrowth afterGrowth
  have readback := EqualityLeafProjectionWorkerReadback.requireEdges_readback paths rows ordinaryRows
    actual.2 after actualChecked.1.coherent.valid afterGrowth
  have outputsSame : outputs = (rows.filter (fun edge => fits paths edge.children.length)).map (rebuild after (requiredChild paths after)) :=
    Option.some.inj (outputReturned.symm.trans readback)
  have outputsResident : ∀ edge ∈ outputs, EdgeResident after edge := by
    intro edge member
    exact edge_grows original.2 after afterGrowth edge ((originalChecked.2 outputs outputReturned) edge member).1
  have rebuiltResident : ∀ edge ∈ rows.filter (fun edge => fits paths edge.children.length),
      EdgeResident after (rebuild after (requiredChild paths after) edge) := by
    intro edge member
    apply outputsResident
    rw [outputsSame]
    exact List.mem_map.mpr ⟨edge, member, rfl⟩
  have normalized := selected_normalization paths rows state after facts afterFacts totalGrowth
    (fun edge member => (rowFacts.2 edge member).1) rebuiltResident
  rw [nodeClosed] at normalized
  have requestExact : run (makeNode outputs) after = (result, after) := by
    rw [outputsSame, normalized]
    cases value with
    | empty =>
        have resultEmpty : result = .empty := by
          have same : some (.empty : Value Symbol Guard) = some result := by simpa only [require_empty, run] using returned
          exact (Option.some.inj same).symm
        subst result
        simp [nodeEdges, makeNode, surviving, canonicalEdges, EnumerationBuilderCaches.canonicalIds, run]
    | reference | union | mu => simp only [EqualityLeafProjectionWorkers.Ordinary] at inputOrdinary
    | node entry canonical depth free =>
        exact require_parent_replay paths proper entry canonical depth free
          (by simpa only [EqualityLeafProjectionWorkers.Ordinary] using inputOrdinary)
          state after facts.coherent.valid result returned actualToAfter
  refine ⟨after, result, afterFacts, actualToAfter, returned, ?_⟩
  exact node_intro leaf _ after result outputs changedRows requestExact

end MicroCFTA.EqualityLeafProjectionRequireParent
