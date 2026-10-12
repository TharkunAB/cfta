import MicroCFTA.InternedEdgeResidency

/-!
# Exact canonical node construction from surviving edge sets

A fixed source context can retain duplicate original rows. Normalized
construction removes duplicates and empty-child rows. Equal surviving edge
sets produce the same complete request, payload, and cache effects.
-/
namespace MicroCFTA.InternedNodeSetCongruence
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency

/-- Equal identity sets determine the complete canonical edge sequence in a coherent cache. -/
theorem canonical_same (state : State Symbol Guard) (coherent : Coherent state)
    (first second : List (EdgeValue Symbol Guard))
    (left : ∀ edge ∈ first, EdgeResident state edge)
    (right : ∀ edge ∈ second, EdgeResident state edge)
    (same : ∀ identity, identity ∈ first.map (fun edge => edge.entry.identity) ↔
      identity ∈ second.map (fun edge => edge.entry.identity)) : canonicalEdges first = canonicalEdges second := by
  apply edge_lists_equal state coherent
  · intro edge member
    exact left edge (canonicalEdges_member first edge member)
  · intro edge member
    exact right edge (canonicalEdges_member second edge member)
  · rw [canonicalEdges_ids, canonicalEdges_ids]
    exact (EnumerationBuilderCaches.canonicalIds_equal _ _).mpr same

/-- Source node construction depends only on the identities of surviving resident edges. -/
theorem makeNode_same_ids (state : State Symbol Guard) (coherent : Coherent state)
    (first second : List (EdgeValue Symbol Guard))
    (left : ∀ edge ∈ first, EdgeResident state edge)
    (right : ∀ edge ∈ second, EdgeResident state edge)
    (same : ∀ identity, identity ∈ (surviving first).map (fun edge => edge.entry.identity) ↔
      identity ∈ (surviving second).map (fun edge => edge.entry.identity)) : makeNode first = makeNode second := by
  have canonical := canonical_same state coherent (surviving first) (surviving second)
    (fun edge member => left edge (List.mem_filter.mp member).1)
    (fun edge member => right edge (List.mem_filter.mp member).1) same
  simp only [makeNode, canonical]

/-- Row order and duplicate occurrence counts do not change the complete normalized request. -/
theorem makeNode_same_members (state : State Symbol Guard) (coherent : Coherent state)
    (first second : List (EdgeValue Symbol Guard))
    (left : ∀ edge ∈ first, EdgeResident state edge)
    (right : ∀ edge ∈ second, EdgeResident state edge)
    (same : ∀ edge, edge ∈ surviving first ↔ edge ∈ surviving second) : makeNode first = makeNode second := by
  apply makeNode_same_ids state coherent first second left right
  intro identity
  simp only [List.mem_map]
  constructor <;> rintro ⟨edge, member, equal⟩
  · exact ⟨edge, (same edge).mp member, equal⟩
  · exact ⟨edge, (same edge).mpr member, equal⟩

/-- Keeping duplicate original parent rows is exact before canonical lowering. -/
theorem makeNode_duplicate (state : State Symbol Guard) (coherent : Coherent state)
    (edges : List (EdgeValue Symbol Guard)) (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    makeNode (edges ++ edges) = makeNode edges := by
  apply makeNode_same_members state coherent (edges ++ edges) edges
    (fun edge member => resident edge (List.mem_append.mp member |>.elim id id)) resident
  intro edge
  simp [surviving]

/-- Retained provenance rows with an empty child contribute no source node edge. -/
theorem makeNode_dead_rows (state : State Symbol Guard) (coherent : Coherent state)
    (dead edges : List (EdgeValue Symbol Guard))
    (residentDead : ∀ edge ∈ dead, EdgeResident state edge)
    (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (emptyChild : ∀ edge ∈ dead, edge.children.any (fun child => child.referenceOf == .empty) = true) :
    makeNode (dead ++ edges) = makeNode edges := by
  apply makeNode_same_members state coherent (dead ++ edges) edges
    (fun edge member => List.mem_append.mp member |>.elim (residentDead edge) (resident edge)) resident
  intro edge
  simp only [surviving, List.filter_append, List.mem_append, List.mem_filter, Bool.not_eq_true']
  constructor
  · rintro (⟨member, live⟩ | member)
    · simp [emptyChild edge member] at live
    · exact member
  · exact Or.inr

/-- After the earlier request completes, an equal surviving set returns its exact record without allocation. -/
theorem set_replay [DecidableEq (EdgeKey Symbol Guard)] (first second : List (EdgeValue Symbol Guard))
    (before after : State Symbol Guard) (valid : Valid before) (coherent : Coherent after)
    (growth : Grows (run (makeNode first) before).2 after)
    (left : ∀ edge ∈ first, EdgeResident after edge)
    (right : ∀ edge ∈ second, EdgeResident after edge)
    (same : ∀ edge, edge ∈ surviving first ↔ edge ∈ surviving second) :
    run (makeNode second) after = ((run (makeNode first) before).1, after) := by
  rw [← makeNode_same_members after coherent first second left right same]
  exact replay (makeNode first) before after valid growth

end MicroCFTA.InternedNodeSetCongruence
