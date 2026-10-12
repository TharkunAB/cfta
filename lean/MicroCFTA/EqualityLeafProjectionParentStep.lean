import MicroCFTA.EqualityLeafProjectionParentCache

/-!
# Actual parent workers on retained original occurrences

The actual source worker runs first on the stored canonical parent. Later
finite preparation evaluates selected original child requests and rebuilt
ancestor edges. The earlier complete result equals reconstruction from
original occurrences, including duplicate and dead rows.
-/
namespace MicroCFTA.EqualityLeafProjectionParentStep
open InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency InternedProbeProvenance
open EqualityLeafProjectionSyntax (Path descendEdits descend fits)
open EqualityLeafProjectionWorkers EqualityLeafProjectionPhysical EqualityLeafProjectionParentCache
open EqualityLeafProjectionWorkerReadback

/-- Ordinary child membership derives the source worker's structural edge invariant. -/
theorem ordinary_edges (edges : List (EdgeValue Symbol Guard))
    (children : ∀ edge ∈ edges, ∀ child ∈ edge.children, Ordinary child) : OrdinaryEdges edges := by
  induction edges with
  | nil => trivial
  | cons edge rest ih =>
      cases edge with
      | mk entry values =>
          refine ⟨?_, ih (fun edge member => children edge (by simp [member]))⟩
          have all : ∀ child ∈ values, Ordinary child := children (.mk entry values) (by simp)
          clear children
          induction values with
          | nil => trivial
          | cons child tail tailIH => exact ⟨all child (by simp), tailIH (fun value member => all value (by simp [member]))⟩

/-- Node normalization retains the ordinary fragment of all original ancestor children. -/
theorem normalized_ordinary [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (coherent : Coherent before) (linked : Linked before)
    (resident : ∀ edge ∈ edges, EdgeResident before edge)
    (ordinary : ∀ edge ∈ edges, ∀ child ∈ edge.children, Ordinary child) :
    OrdinaryEdges (nodeEdges (run (makeNode edges) before).1) := by
  apply ordinary_edges
  intro edge member child present
  rw [makeNode_edges edges before coherent linked resident] at member
  exact ordinary edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1 child present

/-- Actual non-root editing of the normalized parent equals reconstruction from
all original occurrences in the final finite cache. -/
theorem edit_parent [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (meetSafe : ∀ target value, Safe (meet target value))
    (first : Path × Target) (rest : List (Path × Target))
    (noRoot : EqualityLeafProjectionSyntax.atRoot (first :: rest) = none)
    (edges : List (EdgeValue Symbol Guard)) (before current : State Symbol Guard)
    (beforeCoherent : Coherent before) (linked : Linked before) (currentCoherent : Coherent current)
    (resident : ∀ edge ∈ edges, EdgeResident before edge)
    (ordinary : ∀ edge ∈ edges, ∀ child ∈ edge.children, Ordinary child) :
    let request := fun index child => edit meet (descendEdits (first :: rest) index) child
    let result := run (edit meet (first :: rest) (run (makeNode edges) before).1) current
    let prepared := prepare request (fun _ => true) edges result.2
    result.1 = some (run (makeNode (edges.map (rebuild prepared (editedChild meet (first :: rest) prepared)))) prepared).1 := by
  let request := fun index child => edit meet (descendEdits (first :: rest) index) child
  let result := run (edit meet (first :: rest) (run (makeNode edges) before).1) current
  let prepared := prepare request (fun _ => true) edges result.2
  have resultCoherent : Coherent result.2 := edit_coherent meet meetSafe _ _ current currentCoherent
  have preparedFacts := prepare_correct request (fun index child => edit_safe meet meetSafe _ child)
    (fun _ => true) edges result.2 resultCoherent
  have normalized := prepared_parent request (fun index child => edit_safe meet meetSafe _ child)
    (fun index => edit_empty meet _) edges (fun _ => true) before result.2 prepared
    beforeCoherent linked resultCoherent preparedFacts.1 resident (grows_refl prepared)
  have filterAll : ∀ rows : List (EdgeValue Symbol Guard), rows.filter (fun _ => true) = rows :=
    fun _ => List.filter_eq_self.mpr (fun _ _ => rfl)
  simp only [filterAll] at normalized
  have sourceOrdinary := normalized_ordinary edges before beforeCoherent linked resident ordinary
  have sourceRoot := EqualityLeafProjectionUnion.makeNode_ordinary edges before beforeCoherent linked resident
  change makeNode (edges.map (rebuild prepared (editedChild meet (first :: rest) prepared))) =
    makeNode ((nodeEdges (run (makeNode edges) before).1).map (rebuild prepared (editedChild meet (first :: rest) prepared))) at normalized
  change result.1 = some (run (makeNode (edges.map (rebuild prepared (editedChild meet (first :: rest) prepared)))) prepared).1
  cases source : (run (makeNode edges) before).1 with
  | empty =>
      have emptyRequest : makeNode (edges.map (rebuild prepared (editedChild meet (first :: rest) prepared))) = .pure .empty := by
        rw [source] at normalized
        simpa only [nodeEdges, List.map_nil, makeNode, surviving, List.filter_nil,
          canonicalEdges, List.map_nil, EnumerationBuilderCaches.canonicalIds, List.mergeSort_nil, List.eraseDups_nil,
          List.filterMap_nil] using normalized
      rw [emptyRequest]
      simp only [result, source, edit_empty, run]
  | reference | union | mu => simp only [source, EqualityLeafProjectionUnion.OrdinaryRoot] at sourceRoot
  | node entry actual depth free =>
      have checked := edit_node_readback meet first rest entry actual depth free
        (by simpa only [source, nodeEdges] using sourceOrdinary) noRoot current prepared currentCoherent.valid
        (by rw [← source]; exact preparedFacts.2)
      have equality : makeNode (edges.map (rebuild prepared (editedChild meet (first :: rest) prepared))) =
          makeNode (actual.map (rebuild prepared (editedChild meet (first :: rest) prepared))) := by
        simpa only [source, nodeEdges] using normalized
      rw [equality]
      simpa only [result, source] using checked

/-- Actual proper-path requirement on the normalized parent reconstructs only
original rows with the required arity and their completed child readbacks. -/
theorem require_parent [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (proper : fits paths 0 = false)
    (edges : List (EdgeValue Symbol Guard)) (before current : State Symbol Guard)
    (beforeCoherent : Coherent before) (linked : Linked before) (currentCoherent : Coherent current)
    (resident : ∀ edge ∈ edges, EdgeResident before edge)
    (ordinary : ∀ edge ∈ edges, ∀ child ∈ edge.children, Ordinary child) :
    let request := fun index (child : Value Symbol Guard) => require (descend paths index) child
    let select := fun edge : EdgeValue Symbol Guard => fits paths edge.children.length
    let result := run (require paths (run (makeNode edges) before).1) current
    let prepared := prepare request select edges result.2
    result.1 = some (run (makeNode ((edges.filter select).map (rebuild prepared (requiredChild paths prepared)))) prepared).1 := by
  let request := fun index (child : Value Symbol Guard) => require (descend paths index) child
  let select := fun edge : EdgeValue Symbol Guard => fits paths edge.children.length
  let result := run (require paths (run (makeNode edges) before).1) current
  let prepared := prepare request select edges result.2
  have resultCoherent : Coherent result.2 := require_coherent paths _ current currentCoherent
  have preparedFacts := prepare_correct request (fun index child => require_safe _ child)
    select edges result.2 resultCoherent
  have normalized := prepared_parent request (fun index child => require_safe _ child)
    (fun index => require_empty _) edges select before result.2 prepared
    beforeCoherent linked resultCoherent preparedFacts.1 resident (grows_refl prepared)
  have sourceOrdinary := normalized_ordinary edges before beforeCoherent linked resident ordinary
  have sourceRoot := EqualityLeafProjectionUnion.makeNode_ordinary edges before beforeCoherent linked resident
  change makeNode ((edges.filter select).map (rebuild prepared (requiredChild paths prepared))) =
    makeNode (((nodeEdges (run (makeNode edges) before).1).filter select).map (rebuild prepared (requiredChild paths prepared))) at normalized
  change result.1 = some (run (makeNode ((edges.filter select).map (rebuild prepared (requiredChild paths prepared)))) prepared).1
  cases source : (run (makeNode edges) before).1 with
  | empty =>
      have emptyRequest : makeNode ((edges.filter select).map (rebuild prepared (requiredChild paths prepared))) = .pure .empty := by
        rw [source] at normalized
        simpa only [nodeEdges, List.filter_nil, List.map_nil, makeNode, surviving, List.filter_nil,
          canonicalEdges, List.map_nil, EnumerationBuilderCaches.canonicalIds, List.mergeSort_nil, List.eraseDups_nil,
          List.filterMap_nil] using normalized
      rw [emptyRequest]
      simp only [result, source, require_empty, run]
  | reference | union | mu => simp only [source, EqualityLeafProjectionUnion.OrdinaryRoot] at sourceRoot
  | node entry actual depth free =>
      have checked := require_node_readback paths proper entry actual depth free
        (by simpa only [source, nodeEdges] using sourceOrdinary) current prepared currentCoherent.valid
        (by rw [← source]; exact preparedFacts.2)
      have equality : makeNode ((edges.filter select).map (rebuild prepared (requiredChild paths prepared))) =
          makeNode ((actual.filter select).map (rebuild prepared (requiredChild paths prepared))) := by
        simpa only [source, nodeEdges] using normalized
      rw [equality]
      simpa only [result, source] using checked

end MicroCFTA.EqualityLeafProjectionParentStep
