import MicroCFTA.InternedStoredPlanBinderDepthProgress

/-!
# Composition of complete Mu body bounds

The exact old-record alternative remains under a larger bound.
Two successive allocation bounds compose at the same bound.
-/
namespace MicroCFTA.InternedStoredPlanBinderDepthProgress
open InternedConstructorTemplates

/-- A larger body bound retains each exact old-record alternative. -/
theorem Lower.mono {before after : State Symbol Guard} {low high : Nat}
    (lower : Lower before low after) (limited : low ≤ high) : Lower before high after := by
  intro key entry body depth ordinary present
  rcases lower key entry body depth ordinary present with old | small
  · exact Or.inl old
  · exact Or.inr (Nat.lt_of_lt_of_le small limited)

/-- Successive body bounds retain the first heap's exact record alternative. -/
theorem Lower.trans {before middle after : State Symbol Guard} {bound : Nat}
    (first : Lower before bound middle) (second : Lower middle bound after) :
    Lower before bound after := by
  intro key entry body depth ordinary present
  rcases second key entry body depth ordinary present with old | small
  · exact first key entry body depth ordinary old
  · exact Or.inr small

end MicroCFTA.InternedStoredPlanBinderDepthProgress
