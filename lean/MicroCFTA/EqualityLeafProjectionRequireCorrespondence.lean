import MicroCFTA.EqualityLeafProjectionPreparationAvailability

/-!
# Source-first requirement stages on closed occurrence representations

The direct-return and leaf branches have exact represented results. A
proper parent requirement returns first, then selected finite preparation
provides a complete common cache for original-row reconstruction. Original
record, ordinary-input, and child-availability premises are derived from
the closed occurrence representation.
-/
namespace MicroCFTA.EqualityLeafProjectionRequireCorrespondence
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open EqualityLeafProjectionSyntax (Tree Edge Path fits descend)
open EqualityLeafProjectionCompile (Tag)
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionCompileOrdinary
open EqualityLeafProjectionRepresentation EqualityLeafProjectionWorkers
open EqualityLeafProjectionRequireAvailability EqualityLeafProjectionPreparationAvailability
open EqualityLeafProjectionPhysical

/-- The concrete nullary leaf constructor has the source's allocation-free requirement behavior. -/
def LeafRequires [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ input paths state, Facts state → require paths (run (leaf input) state).1 =
    .pure (some (if fits paths 0 then (run (leaf input) state).1 else .empty))

/-- A root-only source requirement returns an exact represented unchanged occurrence. -/
theorem root_only [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (tree : Tree (Tag Symbol Guard) Leaf)
    (paths : List Path) (root : fits paths 0 = true) (state : State Symbol Guard) (value : Value Symbol Guard)
    (represented : Represents leaf tree state value) :
    run (require paths value) state = (some value, state) ∧
      Represents leaf (EqualityLeafProjectionSyntax.require paths tree) state value := by
  refine ⟨?_, ?_⟩
  · unfold require
    simp only [root, ↓reduceIte, run]
  · rw [EqualityLeafProjectionRequireSyntax.require_trivial paths root tree]
    exact represented

/-- A proper child requirement removes an actual represented nullary leaf without allocation. -/
theorem leaf_proper [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leafRequires : LeafRequires leaf)
    (input : Leaf) (paths : List Path) (proper : fits paths 0 = false)
    (state : State Symbol Guard) (facts : Facts state) (value : Value Symbol Guard)
    (represented : Represents leaf (.leaf input) state value) :
    run (require paths value) state = (some .empty, state) ∧
      Represents leaf (EqualityLeafProjectionSyntax.require paths (.leaf input)) state .empty := by
  have closed : run (leaf input) state = (value, state) := represented
  have source := leafRequires input paths state facts
  rw [closed] at source
  simp only [proper, Bool.false_eq_true, ↓reduceIte] at source
  refine ⟨?_, ?_⟩
  · rw [source]
    rfl
  · simp only [EqualityLeafProjectionSyntax.require, proper, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- A proper represented parent requirement derives original-row reconstruction
in a complete later finite cache, after the actual source worker returns. -/
theorem node_stage [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leafAvailable : LeafAvailable leaf) (leafOrdinary : LeafOrdinary leaf)
    (edges : List (Edge (Tag Symbol Guard) Leaf)) (paths : List Path) (proper : fits paths 0 = false)
    (state : State Symbol Guard) (facts : Facts state) (value : Value Symbol Guard)
    (represented : Represents leaf (.node edges) state value) :
    let actual := run (require paths value) state
    ∃ rows after, RepresentsEdges leaf edges state rows ∧ Facts after ∧ Grows actual.2 after ∧
      actual.1 = some (run (makeNode ((rows.filter (fun edge => fits paths edge.children.length)).map
        (rebuild after (requiredChild paths after)))) after).1 := by
  obtain ⟨rows, rowsClosed, nodeClosed⟩ := node_decompose leaf edges state facts.coherent.valid value represented
  have rowsFacts := compileEdges_available leaf leafAvailable edges state facts
  rw [rowsClosed] at rowsFacts
  have parentAvailable := EqualityLeafProjectionRepresentation.available leaf leafAvailable (.node edges) state facts value represented
  have parentOrdinary := compile_ordinary leaf leafAvailable leafOrdinary (.node edges) state facts
  rw [represented] at parentOrdinary
  let actual := run (require paths value) state
  have actualFacts : Facts actual.2 := (require_available paths value state facts parentAvailable).1
  let request := fun index (child : Value Symbol Guard) => require (descend paths index) child
  let select := fun edge : EdgeValue Symbol Guard => fits paths edge.children.length
  let after := EqualityLeafProjectionSelectedCache.prepare request select rows actual.2
  have childInputs : ∀ edge ∈ rows, ChildrenAvailable actual.2 edge.children := by
    intro edge member child present
    exact available_after_run (require paths value) state facts.coherent.valid ((rowsFacts.2 edge member).2 child present)
  have preparedFacts : Facts after := prepare_facts request (fun index child current currentFacts input =>
    require_available _ child current currentFacts input) select rows actual.2 actualFacts childInputs
  have preparedGrowth : Grows actual.2 after := (EqualityLeafProjectionSelectedCache.prepare_correct request
    (fun index child => require_safe _ child) select rows actual.2 actualFacts.coherent).2
  have totalGrowth : Grows state after := grows_trans
    (InternedConstructorTemplates.run_correct (require paths value) state facts.coherent.valid).2 preparedGrowth
  have normalized := EqualityLeafProjectionSelectedCache.prepared_parent request
    (fun index child => require_safe _ child) (fun index => require_empty _) rows select state actual.2 after
    facts.coherent facts.linked actualFacts.coherent preparedFacts.coherent
    (fun edge member => (rowsFacts.2 edge member).1) totalGrowth (grows_refl after)
  rw [nodeClosed] at normalized
  change makeNode ((rows.filter select).map (rebuild after (requiredChild paths after))) =
    makeNode (((nodeEdges value).filter select).map (rebuild after (requiredChild paths after))) at normalized
  refine ⟨rows, after, rowsClosed, preparedFacts, preparedGrowth, ?_⟩
  change actual.1 = some (run (makeNode ((rows.filter select).map (rebuild after (requiredChild paths after)))) after).1
  rw [normalized]
  cases value with
  | empty => simp [actual, require_empty, run, nodeEdges, makeNode, surviving, canonicalEdges, EnumerationBuilderCaches.canonicalIds]
  | reference | union | mu => simp only [EqualityLeafProjectionWorkers.Ordinary] at parentOrdinary
  | node entry original depth free =>
      exact EqualityLeafProjectionWorkerReadback.require_node_readback paths proper entry original depth free
        (by simpa only [EqualityLeafProjectionWorkers.Ordinary] using parentOrdinary)
        state after facts.coherent.valid preparedGrowth

end MicroCFTA.EqualityLeafProjectionRequireCorrespondence
