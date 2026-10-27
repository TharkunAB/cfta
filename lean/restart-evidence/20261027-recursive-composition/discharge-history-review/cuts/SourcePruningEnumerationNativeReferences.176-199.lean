/-- Fixed reference preservation and protected class equivalence retain incoming avoidance. -/
theorem incoming_preserved (before after : EnumerationState.State Symbol EnumGuard)
    (held : Nat) (scs : List Suspended) (incoming : IncomingAvoid held before)
    (inputs : Avoids before.representatives held scs)
    (classes : ∀ uv, UnionFind.SameClass after.representatives held uv ↔
      UnionFind.SameClass before.representatives held uv)
    (effects : ∀ allowed, ReferencesAllowed allowed before → InputsAllowed allowed scs →
      ReferencesAllowed allowed after) : IncomingAvoid held after := by
  have valid := effects (fun uv => ¬UnionFind.SameClass before.representatives held uv) incoming inputs
  intro value member sc listed same
  exact valid value member sc listed ((classes sc.var).mp same)

/-- Actual reference effects and protected old enumerated roots retain global pending references. -/
theorem pending_preserved (before after : EnumerationState.State Symbol EnumGuard) (scs : List Suspended)
    (pending : PendingReferences before) (inputs : InputsPending before scs)
    (origin : EnumeratedOrigin before after)
    (protects : ∀ held fragment, before.values[held]? = some (.enumerated fragment) →
      EnumerationDriver.Protected held before after)
    (effects : ∀ allowed, ReferencesAllowed allowed before → InputsAllowed allowed scs →
      ReferencesAllowed allowed after) : PendingReferences after := by
  intro held fragment stored
  have old := origin held fragment stored
  exact incoming_preserved before after held scs (pending held fragment old) (inputs held fragment old)
    (protects held fragment old).classes effects
