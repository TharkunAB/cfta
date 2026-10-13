import MicroCFTA.MergedSourceSelectionSemantics
import MicroCFTA.MergedColdGraphTransport

/-!
# Original cold-cache language of selected children

The actual returned selection accepts exactly the union of the original
input languages before any comparison or unfolding effects.
-/
namespace MicroCFTA.MergedSelectionOriginalLanguage
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedNestedProvenance
open MergedPhysicalWarmup MergedPhysicalLanguage MergedSourceSelection MergedComparisonFacts Language

/-- Actual cold selection preserves the union of the original cache's operand languages. -/
theorem select_exact [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (available : Values state inputs)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : select clear fuel inputs state = .done retained after)
    (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (term : Term Symbol) :
    (∃ value ∈ retained, EpsilonUnion.Accepts (graph after meaning) value term) ↔
      ∃ value ∈ inputs, EpsilonUnion.Accepts (graph state meaning) value term := by
  rw [MergedSourceSelectionSemantics.select_actual_exact clear fuel inputs state facts prepared available retained after done meaning clearTrue term]
  have effect := (select_verified clear fuel inputs state facts prepared available).effect done
  constructor
  · rintro ⟨value, member, accepted⟩
    exact ⟨value, member, (MergedColdGraphTransport.accepts_stable state after facts effect.facts prepared
      effect.growth effect.history meaning value (available value member) term).mpr accepted⟩
  · rintro ⟨value, member, accepted⟩
    exact ⟨value, member, (MergedColdGraphTransport.accepts_stable state after facts effect.facts prepared
      effect.growth effect.history meaning value (available value member) term).mp accepted⟩

end MicroCFTA.MergedSelectionOriginalLanguage
