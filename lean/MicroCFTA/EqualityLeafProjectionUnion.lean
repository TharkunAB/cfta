import MicroCFTA.EqualityLeafProjectionProduct
import MicroCFTA.InternedUnionRetention

/-!
# Exact physical union for projected ordinary leaves

The source union constructor removes empty operands and repeated node
identities. Its ordinary branch concatenates the stored edge records.
Coherent cache readback retains exactly their complete live row set.
-/
namespace MicroCFTA.EqualityLeafProjectionUnion
open InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency
open InternedFreshProbeKeys InternedProbeProvenance EqualityLeafProjectionPhysical

/-- An ordinary projection has an empty root or an ordinary node root. -/
def OrdinaryRoot : Value Symbol Guard → Prop
  | .empty | .node .. => True
  | _ => False

/-- A nonempty flattened ordinary operand is an ordinary node. -/
def NodeRoot : Value Symbol Guard → Prop
  | .node .. => True
  | _ => False

/-- Flattening an ordinary operand retains only that exact nonempty node. -/
theorem ordinary_member (value selected : Value Symbol Guard) (ordinary : OrdinaryRoot value)
    (member : selected ∈ unionMembers value) : selected = value ∧ NodeRoot selected := by
  cases value <;> simp_all [OrdinaryRoot, NodeRoot, unionMembers]

/-- Ordinary operand concatenation succeeds and reads the literal edge lists. -/
theorem ordinary_edges (values : List (Value Symbol Guard))
    (ordinary : ∀ value ∈ values, NodeRoot value) :
    ordinaryEdges values = some (values.flatMap nodeEdges) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      have head := ordinary first (by simp)
      have tail := ih (fun value member => ordinary value (by simp [member]))
      cases first <;> simp only [NodeRoot] at head <;> try contradiction
      simp [ordinaryEdges, tail, nodeEdges]

/-- Physical source union retains exactly the complete live outgoing edge set. -/
theorem union_edges [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ value ∈ values, Resident state value)
    (ordinary : ∀ value ∈ values, OrdinaryRoot value)
    (live : ∀ value ∈ values, ∀ edge ∈ nodeEdges value, dead edge = false)
    (edge : EdgeValue Symbol Guard) :
    edge ∈ nodeEdges (run (makeUnion values) state).1 ↔
      ∃ value ∈ values, edge ∈ nodeEdges value := by
  let flat := values.flatMap unionMembers
  let members := distinctNodes flat
  have flatFacts : ∀ value ∈ flat, value ∈ values ∧ NodeRoot value := by
    intro value member
    obtain ⟨source, included, selected⟩ := List.mem_flatMap.mp member
    obtain ⟨rfl, isNode⟩ := ordinary_member source value (ordinary source included) selected
    exact ⟨included, isNode⟩
  have flatResident : ∀ value ∈ flat, Resident state value :=
    fun value member => resident value (flatFacts value member).1
  have selected : ∀ value, value ∈ members ↔ value ∈ flat := by
    intro value
    exact ⟨distinctNodes_member flat value, InternedUnionRetention.distinctNodes_retains state coherent flat flatResident value⟩
  have memberFacts : ∀ value ∈ members, value ∈ values ∧ NodeRoot value :=
    fun value member => flatFacts value ((selected value).mp member)
  have memberResident : ∀ value ∈ members, Resident state value :=
    fun value member => resident value (memberFacts value member).1
  have memberEdges : ∀ candidate, candidate ∈ members.flatMap nodeEdges ↔
      ∃ value ∈ values, candidate ∈ nodeEdges value := by
    intro candidate
    constructor
    · intro member
      obtain ⟨value, present, found⟩ := List.mem_flatMap.mp member
      exact ⟨value, (memberFacts value present).1, found⟩
    · rintro ⟨value, present, found⟩
      have root := ordinary value present
      have flattened : value ∈ unionMembers value := by
        cases value <;> simp_all [OrdinaryRoot, nodeEdges, unionMembers]
      exact List.mem_flatMap.mpr ⟨value, (selected value).mpr (List.mem_flatMap.mpr ⟨value, present, flattened⟩), found⟩
  have concatenated := ordinary_edges members (fun value member => (memberFacts value member).2)
  have edgesResident := ordinaryEdges_resident members _ state linked memberResident concatenated
  have edgesLive : ∀ candidate ∈ members.flatMap nodeEdges, dead candidate = false := by
    intro candidate present
    obtain ⟨value, included, found⟩ := (memberEdges candidate).mp present
    exact live value included candidate found
  have normalized : ∀ candidate, candidate ∈ nodeEdges (run (makeNode (members.flatMap nodeEdges)) state).1 ↔
      candidate ∈ members.flatMap nodeEdges := by
    intro candidate
    rw [makeNode_edges _ state coherent linked edgesResident,
      normalized_member state coherent _ edgesResident]
    exact ⟨And.left, fun member => ⟨member, edgesLive candidate member⟩⟩
  cases shape : members with
  | nil =>
      have sourceShape : distinctNodes (values.flatMap unionMembers) = [] := shape
      rw [← memberEdges edge]
      simp [makeUnion, sourceShape, run, shape, nodeEdges]
  | cons first rest =>
      cases rest with
      | nil =>
          have sourceShape : distinctNodes (values.flatMap unionMembers) = [first] := shape
          rw [← memberEdges edge]
          simp [makeUnion, sourceShape, run, shape]
      | cons second tail =>
          have sourceShape : distinctNodes (values.flatMap unionMembers) = first :: second :: tail := shape
          have sourceEdges : ordinaryEdges (first :: second :: tail) = some (members.flatMap nodeEdges) := by
            rw [← shape]
            exact concatenated
          simp only [makeUnion, sourceShape, sourceEdges]
          exact (normalized edge).trans (memberEdges edge)

/-- Projection union preserves the exact set of full source edge keys. -/
theorem union_keys [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ value ∈ values, Resident state value)
    (ordinary : ∀ value ∈ values, OrdinaryRoot value)
    (live : ∀ value ∈ values, ∀ edge ∈ nodeEdges value, dead edge = false)
    (key : EdgeKey Symbol Guard) :
    (∃ edge ∈ nodeEdges (run (makeUnion values) state).1, edge.entry.key = key) ↔
      ∃ value ∈ values, ∃ edge ∈ nodeEdges value, edge.entry.key = key := by
  simp only [union_edges values state coherent linked resident ordinary live]
  constructor
  · rintro ⟨edge, ⟨value, present, found⟩, same⟩
    exact ⟨value, present, edge, found, same⟩
  · rintro ⟨value, present, edge, found, same⟩
    exact ⟨edge, ⟨value, present, found⟩, same⟩

/-- Actual canonical ordinary construction has no recursive or union root. -/
theorem makeNode_ordinary [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    OrdinaryRoot (run (makeNode edges) state).1 := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge := by
    intro edge member
    exact resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · trivial
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback (first :: rest) state coherent linked
      (by simpa only [same] using selected)
    simp only [run, exactResult, identifyNode, OrdinaryRoot]

/-- The actual nullary builder establishes ordinary roots and live edges. -/
theorem nullary_shape [DecidableEq (EdgeKey Symbol Guard)]
    (rows : List (Symbol × Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state) :
    OrdinaryRoot (run (EqualityLeafProjectionNullary.build rows) state).1 ∧
      ∀ edge ∈ nodeEdges (run (EqualityLeafProjectionNullary.build rows) state).1, dead edge = false := by
  let output := run (EqualityLeafProjectionWorkers.sequence (EqualityLeafProjectionNullary.requests rows)) state
  have checked := EqualityLeafProjectionNullary.completed_rows rows state coherent
  have rowsLinked := EqualityLeafProjectionNullary.rows_linked rows state coherent linked
  simp only [EqualityLeafProjectionNullary.build, run_bind]
  refine ⟨makeNode_ordinary output.1 output.2 checked.1 rowsLinked (fun edge member => (checked.2.1 edge member).1), ?_⟩
  intro edge member
  rw [makeNode_edges output.1 output.2 checked.1 rowsLinked (fun edge member => (checked.2.1 edge member).1)] at member
  exact ((normalized_member output.2 checked.1 output.1 (fun edge member => (checked.2.1 edge member).1) edge).mp member).2

open EqualityLeafProjectionLeafCache (ConstraintKey Leaf)
noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Readback of any physical ordinary leaf union is the union of its row predicates. -/
theorem union_read (values : List (Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ value ∈ values, Resident state value)
    (ordinary : ∀ value ∈ values, OrdinaryRoot value)
    (live : ∀ value ∈ values, ∀ edge ∈ nodeEdges value, dead edge = false) :
    EqualityLeafProjectionLeafCache.read (initial := initial) (run (makeUnion values) state).1 =
      fun symbol row => ∃ value ∈ values, EqualityLeafProjectionLeafCache.read value symbol row := by
  funext symbol row
  exact propext (union_keys values state coherent linked resident ordinary live _)

/-- The physical projection union of two constructed leaves has exactly their row union. -/
theorem built_union_read (first second : Leaf initial symbols)
    (leftState rightState state : State (Fin symbols) ConstraintKey)
    (leftCoherent : Coherent leftState) (rightCoherent : Coherent rightState) (coherent : Coherent state)
    (leftLinked : Linked leftState) (rightLinked : Linked rightState) (linked : Linked state)
    (leftGrowth : Grows (run (EqualityLeafProjectionLeafCache.build first) leftState).2 state)
    (rightGrowth : Grows (run (EqualityLeafProjectionLeafCache.build second) rightState).2 state) :
    EqualityLeafProjectionLeafCache.read (run (makeUnion
      [(run (EqualityLeafProjectionLeafCache.build first) leftState).1,
       (run (EqualityLeafProjectionLeafCache.build second) rightState).1]) state).1 =
      fun symbol row => first symbol row ∨ second symbol row := by
  have leftShape := nullary_shape (EqualityLeafProjectionProduct.declarations first) leftState leftCoherent leftLinked
  have rightShape := nullary_shape (EqualityLeafProjectionProduct.declarations second) rightState rightCoherent rightLinked
  rw [← EqualityLeafProjectionProduct.leaf_build first] at leftShape
  rw [← EqualityLeafProjectionProduct.leaf_build second] at rightShape
  have leftResident := resident_grows _ state leftGrowth _ (EqualityLeafProjectionLeafCache.build_resident first leftState leftCoherent)
  have rightResident := resident_grows _ state rightGrowth _ (EqualityLeafProjectionLeafCache.build_resident second rightState rightCoherent)
  rw [union_read _ state coherent linked
    (by intro value present; simp only [List.mem_cons, List.not_mem_nil, or_false] at present; rcases present with rfl | rfl <;> assumption)
    (by intro value present; simp only [List.mem_cons, List.not_mem_nil, or_false] at present; rcases present with rfl | rfl; exact leftShape.1; exact rightShape.1)
    (by intro value present; simp only [List.mem_cons, List.not_mem_nil, or_false] at present; rcases present with rfl | rfl; exact leftShape.2; exact rightShape.2)]
  funext symbol row
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    EqualityLeafProjectionLeafCache.build_read first leftState leftCoherent leftLinked,
    EqualityLeafProjectionLeafCache.build_read second rightState rightCoherent rightLinked]

end MicroCFTA.EqualityLeafProjectionUnion
