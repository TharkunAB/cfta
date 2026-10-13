import MicroCFTA.EqualityLeafProjectionPhysical
import MicroCFTA.MergedSourceGrouping

/-!
# Row counts after actual node normalization and readback

Canonical ordering retains at most one row for each edge identity.
Empty-child removal and canonical ordering cannot increase the number
of rows selected by any predicate, including a source symbol/arity key.
-/
namespace MicroCFTA.MergedNodeRowBounds
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency

/-- Canonical edge identity uniqueness gives uniqueness of the retained complete records. -/
theorem canonical_nodup (edges : List (EdgeValue Symbol Guard)) : (canonicalEdges edges).Nodup := by
  have ids : ((canonicalEdges edges).map (fun edge => edge.entry.identity)).Nodup := by
    rw [canonicalEdges_ids]
    exact EnumerationBuilderCaches.canonicalIds_nodup _
  exact List.Pairwise.of_map (fun edge => edge.entry.identity)
    (fun first second different same => different (congrArg (fun edge => edge.entry.identity) same)) ids

/-- Canonical ordering cannot increase any selected row count. -/
theorem canonical_filter_length (edges : List (EdgeValue Symbol Guard)) (select : EdgeValue Symbol Guard → Bool) :
    ((canonicalEdges edges).filter select).length ≤ (edges.filter select).length := by
  apply List.Nodup.length_le_of_subset ((canonical_nodup edges).filter select)
  intro edge member
  obtain ⟨present, selected⟩ := List.mem_filter.mp member
  exact List.mem_filter.mpr ⟨canonicalEdges_member edges edge present, selected⟩

/-- Removal of dead rows and duplicate identities cannot increase any selected row count. -/
theorem normalized_filter_length (edges : List (EdgeValue Symbol Guard)) (select : EdgeValue Symbol Guard → Bool) :
    ((canonicalEdges (surviving edges)).filter select).length ≤ (edges.filter select).length := by
  apply List.Nodup.length_le_of_subset ((canonical_nodup (surviving edges)).filter select)
  intro edge member
  obtain ⟨present, selected⟩ := List.mem_filter.mp member
  exact List.mem_filter.mpr ⟨(List.mem_filter.mp (canonicalEdges_member (surviving edges) edge present)).1, selected⟩

/-- Actual complete node readback retains every per-predicate normalized row bound. -/
theorem makeNode_filter_length [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) (select : EdgeValue Symbol Guard → Bool) :
    ((nodeEdges (run (makeNode edges) state).1).filter select).length ≤ (edges.filter select).length := by
  rw [EqualityLeafProjectionPhysical.makeNode_edges edges state coherent linked resident]
  exact normalized_filter_length edges select

/-- Actual node normalization never increases the total row count. -/
theorem makeNode_length [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    (nodeEdges (run (makeNode edges) state).1).length ≤ edges.length := by
  rw [EqualityLeafProjectionPhysical.makeNode_edges edges state coherent linked resident]
  apply List.Nodup.length_le_of_subset (canonical_nodup (surviving edges))
  intro edge member
  exact (List.mem_filter.mp (canonicalEdges_member (surviving edges) edge member)).1

/-- Each actual source symbol/arity class inherits its supplied row bound. -/
theorem makeNode_key_bound [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state) (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (key : Symbol × Nat) (limit : Nat)
    (bounded : (edges.filter (fun edge => decide (MergedSourceGrouping.groupKey edge = key))).length ≤ limit) :
    ((nodeEdges (run (makeNode edges) state).1).filter
      (fun edge => decide (MergedSourceGrouping.groupKey edge = key))).length ≤ limit :=
  Nat.le_trans (makeNode_filter_length edges state coherent linked resident _) bounded

end MicroCFTA.MergedNodeRowBounds
