/-- A complete assignment satisfies forest equalities, stored slots and residual guards. -/
def Satisfies (language : EnumerationCorrectness.NodeLanguage Symbol)
    (meaning : Guard → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (state : State Symbol Guard) : Prop :=
  (FlatUnionFind.Satisfies state.representatives assignment ∧
    heapSatisfies (EnumerationCorrectness.heap language state.values) assignment) ∧
      EnumerationCorrectness.guardsHold meaning assignment state.obligations

/-- Related complete cores permit exactly the same full assignments. -/
theorem related_satisfies (related : Related flat earlier)
    (language : EnumerationCorrectness.NodeLanguage Symbol)
    (meaning : Guard → Term Symbol → Prop) (assignment : Nat → Term Symbol) :
    EnumerationCorrectness.Satisfies language meaning assignment earlier ↔
      Satisfies language meaning assignment flat := by
  simp only [EnumerationCorrectness.Satisfies, Fragments.stateSatisfies, Satisfies,
    FlatUnionFind.represents_satisfies related.representatives, related.values, related.obligations]
