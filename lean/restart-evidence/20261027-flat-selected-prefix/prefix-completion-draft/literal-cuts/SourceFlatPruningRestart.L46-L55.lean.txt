/-- Complete related caches have the same pure restart decision. -/
theorem decision_related (related : Related flat earlier)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing) :
    decision stop order metadata flat = SourcePruningEnumerationRestart.decision stop order metadata earlier := by
  cases stop <;>
    simp only [decision, next, candidates, SourcePruningEnumerationRestart.decision,
      EnumerationPureSelection.next, EnumerationPureSelection.find, EnumerationIndexSelection.candidates,
      related.core.counter, related.expandable, related.waiting]
  all_goals rfl
