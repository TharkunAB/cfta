    exact restrictionExact.mpr ⟨mergedSatisfies, nodeHolds, fun sc member => inherited sc (List.mem_filter.mp member).1⟩

/-- Every inherited trie has the canonical finite-map representation. -/
def ValidSuspended (scs : List Suspended) : Prop := ∀ sc ∈ scs, EqualityTrie.Valid sc.trie

/-- Descent preserves the canonical trie representation. -/
theorem descend_valid (scs : List Suspended) (index : Nat) (valid : ValidSuspended scs) :
