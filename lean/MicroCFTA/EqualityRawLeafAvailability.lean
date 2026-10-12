import MicroCFTA.EqualityRawLeafProgress
import MicroCFTA.EqualityLeafProjectionCompileOrdinary

/-!
# Complete raw leaf payloads in finite occurrence compilation

Rejected sentinel requests retain their complete EmptyNode child. Accepted
rows have no children. Both branches preserve all compiler cache facts.
-/
namespace MicroCFTA.EqualityRawLeafAvailability
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedFreshProbeKeys InternedEdgeResidency InternedProbeProvenance
open EqualityRawLeafConstruction EqualityLeafProjectionCompileAvailability
open EqualityLeafProjectionWorkers (sequence)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Both accepted and rejected source requests retain complete available child records. -/
theorem request_available [DecidableEq Symbol] (row : Symbol × Guard Formula)
    (state : State Symbol ConstraintKey) (facts : Facts state) :
    let result := run (request row) state
    Facts result.2 ∧ EdgeResident result.2 result.1 ∧ ∀ child ∈ result.1.children, Available result.2 child := by
  unfold request
  split
  · have available := makeEdge_available row.1 (some [], row.2) [] state facts.coherent facts.cached (by simp)
    have linked := makeEdge_linked row.1 (some [], row.2) [] state facts.coherent facts.linked
    exact ⟨⟨available.1, available.2.1, linked.1⟩, linked.2, available.2.2⟩
  · have available := makeEdge_available row.1 (some [], Guard.top) [.empty] state facts.coherent facts.cached (by
      intro value member
      have same : value = .empty := by simpa using member
      subst value
      exact empty_available state)
    have linked := makeEdge_linked row.1 (some [], Guard.top) [.empty] state facts.coherent facts.linked
    exact ⟨⟨available.1, available.2.1, linked.1⟩, linked.2, available.2.2⟩

/-- Every original row occurrence keeps its complete payload through later requests. -/
theorem rows_available [DecidableEq Symbol] (rows : List (Symbol × Guard Formula))
    (state : State Symbol ConstraintKey) (facts : Facts state) :
    let result := run (sequence (requests rows)) state
    Facts result.2 ∧ ∀ edge ∈ result.1, EdgeResident result.2 edge ∧
      ∀ child ∈ edge.children, Available result.2 child := by
  induction rows generalizing state with
  | nil => exact ⟨facts, by simp [requests, sequence, run]⟩
  | cons first rest ih =>
      let head := run (request first) state
      have headFacts := request_available first state facts
      let tail := run (sequence (requests rest)) head.2
      have tailFacts := ih head.2 headFacts.1
      have growth : Grows head.2 tail.2 := (InternedConstructorTemplates.run_correct _ head.2 headFacts.1.coherent.valid).2
      simp only [requests, List.map_cons, sequence, run_bind, run]
      refine ⟨tailFacts.1, ?_⟩
      intro edge member
      change edge ∈ head.1 :: tail.1 at member
      rcases List.mem_cons.mp member with same | later
      · subst edge
        exact ⟨edge_grows head.2 tail.2 growth head.1 headFacts.2.1,
          fun child present => available_after_run (sequence (requests rest)) head.2 headFacts.1.coherent.valid
            (headFacts.2.2 child present)⟩
      · exact tailFacts.2 edge later

/-- Actual raw node construction derives the full compiler payload contract. -/
theorem build_available [DecidableEq Symbol] (rows : List (Symbol × Guard Formula))
    (state : State Symbol ConstraintKey) (facts : Facts state) :
    Facts (run (build rows) state).2 ∧ Available (run (build rows) state).2 (run (build rows) state).1 := by
  let compiled := run (sequence (requests rows)) state
  have rowFacts := rows_available rows state facts
  have available := makeNode_available compiled.1 compiled.2 rowFacts.1.coherent rowFacts.1.cached (by
    intro child member
    obtain ⟨edge, included, present⟩ := List.mem_flatMap.mp member
    exact (rowFacts.2 edge included).2 child present)
  have linked := makeNode_linked compiled.1 compiled.2 rowFacts.1.linked (fun edge member => (rowFacts.2 edge member).1)
  simp only [build, run_bind]
  exact ⟨⟨available.1, available.2.1, linked⟩, available.2.2⟩

/-- Raw initial guards instantiate finite occurrence compilation without an admission premise. -/
theorem raw_leaves : LeafAvailable (fun rows : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial) =>
    build (declarations rows)) := fun _ state facts => build_available _ state facts

/-- Every surviving raw source edge has an empty complete ordered child payload. -/
theorem built_nullary (rows : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (edge : EdgeValue (Fin symbols) ConstraintKey)
    (member : edge ∈ nodeEdges (run (build (declarations rows)) state).1) : edge.children = [] := by
  let result := run (build (declarations rows)) state
  have available := build_available (declarations rows) state facts
  have resident := resident_edges result.2 available.1.linked result.1 available.2.resident edge member
  have fields := (available.1.coherent.edges _ edge resident).2.2
  obtain ⟨row, _, _, same⟩ := (build_keys _ state facts.coherent facts.linked edge.entry.key).mp ⟨edge, member, rfl⟩
  apply List.map_eq_nil_iff.mp
  exact fields.trans (congrArg EdgeKey.children same).symm

/-- The raw constructor produces an ordinary root after sentinel removal. -/
theorem built_root [DecidableEq Symbol] (rows : List (Symbol × Guard Formula))
    (state : State Symbol ConstraintKey) (facts : Facts state) :
    EqualityLeafProjectionUnion.OrdinaryRoot (run (build rows) state).1 := by
  let output := run (sequence (requests rows)) state
  have checked := rows_available rows state facts
  simp only [build, run_bind]
  exact EqualityLeafProjectionUnion.makeNode_ordinary output.1 output.2 checked.1.coherent checked.1.linked
    (fun edge member => (checked.2 edge member).1)

/-- Raw leaves derive the complete ordinary-value property required by physical path workers. -/
theorem raw_ordinary : EqualityLeafProjectionCompileOrdinary.LeafOrdinary
    (fun rows : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial) => build (declarations rows)) := by
  intro rows state facts
  have root := built_root (declarations rows) state facts
  have children := built_nullary rows state facts
  have ordinary := EqualityLeafProjectionParentStep.ordinary_edges
    (nodeEdges (run (build (declarations rows)) state).1) (by
      intro edge member child present
      rw [children edge member] at present
      cases present)
  cases shape : (run (build (declarations rows)) state).1 with
  | empty => trivial
  | node => simpa only [shape, nodeEdges, EqualityLeafProjectionWorkers.Ordinary] using ordinary
  | reference | union | mu => simp only [shape, EqualityLeafProjectionUnion.OrdinaryRoot] at root

/-- The raw nullary required-path worker returns its exact record without allocation. -/
theorem built_require (paths : List EqualityLeafProjectionSyntax.Path)
    (rows : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) :
    EqualityLeafProjectionWorkers.require paths (run (build (declarations rows)) state).1 =
      .pure (some (if EqualityLeafProjectionSyntax.fits paths 0 then
        (run (build (declarations rows)) state).1 else .empty)) :=
  EqualityLeafProjectionLeafWorkers.require_nullary paths _ (built_root _ state facts) (built_nullary rows state facts)

end MicroCFTA.EqualityRawLeafAvailability
