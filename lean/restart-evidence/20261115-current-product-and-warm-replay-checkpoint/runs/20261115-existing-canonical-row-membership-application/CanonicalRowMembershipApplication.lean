import MicroCFTA.InternedNodeSetCongruence
import MicroCFTA.InternedNestedFacts

/-!
# Existing canonical row equality from physical membership

This application uses the existing canonical_same theorem.
No new public theorem or canonicalization framework is required.
-/
namespace MicroCFTA.CanonicalRowMembershipApplication
open InternedConstructorTemplates InternedNestedFacts InternedEdgeResidency

set_option autoImplicit false

example {Symbol Guard : Type}
    (heap : State Symbol Guard) (facts : Facts heap)
    (left right : List (EdgeValue Symbol Guard))
    (leftResident : ∀ row ∈ left, EdgeResident heap row)
    (rightResident : ∀ row ∈ right, EdgeResident heap row)
    (same : ∀ row, row ∈ left ↔ row ∈ right) :
    canonicalEdges left = canonicalEdges right := by
  apply InternedNodeSetCongruence.canonical_same heap facts.coherent
    left right leftResident rightResident
  intro identity
  simp only [List.mem_map]
  constructor <;> rintro ⟨row, member, identified⟩
  · exact ⟨row, (same row).mp member, identified⟩
  · exact ⟨row, (same row).mpr member, identified⟩

end MicroCFTA.CanonicalRowMembershipApplication
