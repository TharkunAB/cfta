import MicroCFTA.EqualityLeafProjectionCompile

/-!
# Actual nullary required-path execution

Every physical row from the nullary constructor has an empty child list.
A proper required child path therefore removes all rows before any child
recursion or new cache request. Root-only requirements return the original
complete record directly.
-/
namespace MicroCFTA.EqualityLeafProjectionLeafWorkers
open InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency
open EqualityLeafProjectionSyntax (Path fits)
open EqualityLeafProjectionPhysical EqualityLeafProjectionUnion
open EqualityLeafProjectionWorkers (require requireEdges bindOptional)

/-- Canonical physical nullary construction retains only empty child lists. -/
theorem nullary_children [DecidableEq (EdgeKey Symbol Guard)]
    (rows : List (Symbol × Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state) :
    ∀ edge ∈ nodeEdges (run (EqualityLeafProjectionNullary.build rows) state).1, edge.children = [] := by
  let output := run (EqualityLeafProjectionWorkers.sequence (EqualityLeafProjectionNullary.requests rows)) state
  have checked := EqualityLeafProjectionNullary.completed_rows rows state coherent
  have rowsLinked := EqualityLeafProjectionNullary.rows_linked rows state coherent linked
  intro edge member
  simp only [EqualityLeafProjectionNullary.build, run_bind] at member
  rw [makeNode_edges output.1 output.2 checked.1 rowsLinked (fun edge member => (checked.2.1 edge member).1)] at member
  exact (checked.2.1 edge (List.mem_filter.mp (InternedProbeProvenance.canonicalEdges_member _ edge member)).1).2

/-- A required child position rejects every nullary row before child evaluation. -/
theorem requireEdges_nullary (paths : List Path) (proper : fits paths 0 = false)
    (edges : List (EdgeValue Symbol Guard)) (nullary : ∀ edge ∈ edges, edge.children = []) :
    requireEdges paths edges = .pure (some []) := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
      cases edge with
      | mk entry children =>
          have empty : children = [] := nullary (.mk entry children) (by simp)
          subst children
          simp only [requireEdges, List.length_nil, proper, Bool.false_eq_true, ↓reduceIte]
          exact ih (fun edge member => nullary edge (by simp [member]))

/-- The source nullary required-path worker has an exact allocation-free result. -/
theorem require_nullary (paths : List Path) (value : Value Symbol Guard)
    (ordinary : OrdinaryRoot value) (nullary : ∀ edge ∈ nodeEdges value, edge.children = []) :
    require paths value = .pure (some (if fits paths 0 then value else .empty)) := by
  by_cases proper : fits paths 0 = true
  · unfold require
    simp only [proper, ↓reduceIte]
  · have rejected : fits paths 0 = false := Bool.eq_false_iff.mpr proper
    cases value <;> simp only [OrdinaryRoot] at ordinary <;> try contradiction
    · simp only [require, rejected, Bool.false_eq_true, ↓reduceIte]
    · rename_i entry edges depth free
      have rows := requireEdges_nullary paths rejected edges nullary
      simp only [require, rejected, Bool.false_eq_true, ↓reduceIte, rows]
      simp [bindOptional, Work.bind, makeNode, canonicalEdges, surviving, EnumerationBuilderCaches.canonicalIds]

/-- Constructed source leaves discharge both finite-root and nullary-row premises. -/
theorem built_require [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (rows : List (Symbol × Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state) :
    require paths (run (EqualityLeafProjectionNullary.build rows) state).1 =
      .pure (some (if fits paths 0 then (run (EqualityLeafProjectionNullary.build rows) state).1 else .empty)) :=
  require_nullary paths _ (nullary_shape rows state coherent linked).1 (nullary_children rows state coherent linked)

end MicroCFTA.EqualityLeafProjectionLeafWorkers
