import MicroCFTA.EqualityLeafProjectionRepresentation

/-!
# Exact reconstruction from ordinary outgoing records

A completed ordinary constructor replays from its own outgoing edges.
This property derives complete-record equality from physical edge sets
without assuming that every possible request resides in one finite cache.
-/
namespace MicroCFTA.EqualityOrdinaryReadback
open InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency
open InternedFreshProbeKeys InternedProbeProvenance EqualityLeafProjectionPhysical

/-- Reconstruct this complete ordinary value from its own resident outgoing edges. -/
def Normal [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  run (makeNode (nodeEdges value)) state = (value, state)

/-- An exact ordinary readback remains exact after further record-table growth. -/
theorem normal_grows [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (valid : Valid before) (growth : Grows before after) (value : Value Symbol Guard) (normal : Normal before value) :
    Normal after value := by
  unfold Normal at normal ⊢
  have requestGrowth : Grows (run (makeNode (nodeEdges value)) before).2 after := by
    rw [normal]
    exact growth
  simpa only [normal] using replay (makeNode (nodeEdges value)) before after valid requestGrowth

/-- The literal empty value is already a complete ordinary normal form. -/
theorem empty_normal [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) :
    Normal state (.empty : Value Symbol Guard) := by
  simp [Normal, nodeEdges, makeNode, canonicalEdges, surviving, EnumerationBuilderCaches.canonicalIds, run]

/-- Actual source node construction replays exactly from its completed normalized edges. -/
theorem makeNode_normal [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (before after : State Symbol Guard) (coherent : Coherent before) (linked : Linked before)
    (afterCoherent : Coherent after) (resident : ∀ edge ∈ edges, EdgeResident before edge)
    (growth : Grows (run (makeNode edges) before).2 after) :
    Normal after (run (makeNode edges) before).1 := by
  have earlier : Grows before after := grows_trans (InternedConstructorTemplates.run_correct _ before coherent.valid).2 growth
  have readback := makeNode_edges edges before coherent linked resident
  have selected : ∀ edge ∈ nodeEdges (run (makeNode edges) before).1, EdgeResident after edge := by
    intro edge member
    rw [readback] at member
    exact edge_grows before after earlier edge (resident edge ((normalized_member before coherent edges resident edge).mp member).1)
  apply InternedNodeSetCongruence.set_replay edges _ before after coherent.valid afterCoherent growth
    (fun edge member => edge_grows before after earlier edge (resident edge member)) selected
  intro edge
  simp only [surviving, List.mem_filter, Bool.not_eq_true']
  rw [readback, normalized_member before coherent edges resident edge]
  change (edge ∈ edges ∧ dead edge = false) ↔ ((edge ∈ edges ∧ dead edge = false) ∧ dead edge = false)
  exact ⟨fun present => ⟨present, present.2⟩, And.left⟩

/-- Equal resident complete-key sets determine equal actual ordinary readback records. -/
theorem keys_ext [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (coherent : Coherent state)
    (first second : Value Symbol Guard) (left : Normal state first) (right : Normal state second)
    (leftResident : ∀ edge ∈ nodeEdges first, EdgeResident state edge)
    (rightResident : ∀ edge ∈ nodeEdges second, EdgeResident state edge)
    (same : ∀ key, (∃ edge ∈ nodeEdges first, edge.entry.key = key) ↔
      (∃ edge ∈ nodeEdges second, edge.entry.key = key)) : first = second := by
  have members : ∀ edge, edge ∈ nodeEdges first ↔ edge ∈ nodeEdges second := by
    intro edge
    constructor
    · intro present
      obtain ⟨other, member, key⟩ := (same edge.entry.key).mp ⟨edge, present, rfl⟩
      have found := rightResident other member
      unfold EdgeResident at found
      rw [key, leftResident edge present] at found
      have equal : edge = other := Option.some.inj found
      exact equal.symm ▸ member
    · intro present
      obtain ⟨other, member, key⟩ := (same edge.entry.key).mpr ⟨edge, present, rfl⟩
      have found := leftResident other member
      unfold EdgeResident at found
      rw [key, rightResident edge present] at found
      have equal : edge = other := Option.some.inj found
      exact equal.symm ▸ member
  have requests := InternedNodeSetCongruence.makeNode_same_members state coherent (nodeEdges first) (nodeEdges second)
    leftResident rightResident (fun edge => by simp only [surviving, List.mem_filter, members edge])
  have outputs := congrArg (fun work => run work state) requests
  rw [left, right] at outputs
  exact (Prod.mk.inj outputs).1

/-- Ordinary source union preserves reconstruction from its exact outgoing records. -/
theorem makeUnion_normal [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ value ∈ values, Resident state value)
    (ordinary : ∀ value ∈ values, EqualityLeafProjectionUnion.OrdinaryRoot value)
    (normal : ∀ value ∈ values, Normal state value) :
    Normal (run (makeUnion values) state).2 (run (makeUnion values) state).1 := by
  let members := distinctNodes (values.flatMap unionMembers)
  have memberFacts : ∀ value ∈ members, value ∈ values ∧ EqualityLeafProjectionUnion.NodeRoot value := by
    intro value member
    obtain ⟨source, included, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ _ member)
    obtain ⟨rfl, root⟩ := EqualityLeafProjectionUnion.ordinary_member source value (ordinary source included) selected
    exact ⟨included, root⟩
  have concatenated := EqualityLeafProjectionUnion.ordinary_edges members (fun value member => (memberFacts value member).2)
  have edgesResident := ordinaryEdges_resident members _ state linked
    (fun value member => resident value (memberFacts value member).1) concatenated
  cases shape : members with
  | nil =>
      have sourceShape : distinctNodes (values.flatMap unionMembers) = [] := shape
      simpa only [makeUnion, sourceShape, run] using empty_normal state
  | cons first rest =>
      cases rest with
      | nil =>
          have sourceShape : distinctNodes (values.flatMap unionMembers) = [first] := shape
          have firstNormal := normal first (memberFacts first (by simp only [shape, List.mem_singleton])).1
          simpa only [makeUnion, sourceShape, run] using firstNormal
      | cons second tail =>
          have sourceShape : distinctNodes (values.flatMap unionMembers) = first :: second :: tail := shape
          have sourceEdges : ordinaryEdges (first :: second :: tail) = some (members.flatMap nodeEdges) := by
            rw [← shape]
            exact concatenated
          simp only [makeUnion, sourceShape, sourceEdges]
          exact makeNode_normal _ state _ coherent linked
            (InternedErasedEdgeReplay.run_coherent _ state (makeNode_safe _) coherent) edgesResident (grows_refl _)

end MicroCFTA.EqualityOrdinaryReadback
