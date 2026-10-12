import MicroCFTA.InternedFreeOccurrenceNormalization

/-!
# Exact free-occurrence costs of ordinary source construction

Source node normalization retains precisely the occurrences in its live
input edges. Complete cache readback cannot introduce another occurrence.
-/
namespace MicroCFTA.InternedFreeOccurrenceNode
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedEdgeResidency InternedFreeOccurrenceRank InternedFreeOccurrenceNormalization
open InternedBinderProtocol (Reference)

/-- Actual ordinary normalization has exactly the costs of its surviving original edges. -/
theorem makeNode_cost_iff [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) (item : Reference × Nat) :
    item ∈ costs (run (makeNode edges) state).1 ↔
      ∃ edge ∈ edges, edge.children.any (fun child => child.referenceOf == .empty) = false ∧
        ∃ child ∈ edge.children, item ∈ costs child := by
  rw [makeNode_costs edges state coherent linked resident, edge_member]
  constructor
  · rintro ⟨edge, selected, child, member, occurrence⟩
    have survived := List.mem_filter.mp (canonicalEdges_member _ edge selected)
    refine ⟨edge, survived.1, ?_, child, member, occurrence⟩
    simpa using survived.2
  · rintro ⟨edge, member, live, child, included, occurrence⟩
    have survived : edge ∈ surviving edges := by simp [surviving, member, live]
    exact ⟨edge, canonicalEdges_retains state coherent _ edge
      (fun edge present => resident edge (List.mem_filter.mp present).1) survived, child, included, occurrence⟩

end MicroCFTA.InternedFreeOccurrenceNode
