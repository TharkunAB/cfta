/-- Core ancestry updates use the same raw variable and exact ancestry lists. -/
theorem inheritAncestry_related (related : Related flat earlier) (uv : Nat) :
    Results Related (inheritAncestry uv flat) (EnumerationState.inheritAncestry uv earlier) := by
  change Results Related
    [.ok ((), {flat with recursionAncestry := fun other =>
      if other = uv then (flat.expansionAncestry ++ flat.recursionAncestry uv).eraseDups
      else flat.recursionAncestry other})]
    [.ok ((), {earlier with recursionAncestry := fun other =>
      if other = uv then (earlier.expansionAncestry ++ earlier.recursionAncestry uv).eraseDups
      else earlier.recursionAncestry other})]
  refine .cons (.ok () ⟨related.valid, related.representatives, related.counter,
    related.values, related.obligations, ?_, related.expansionAncestry⟩) .nil
  rw [related.expansionAncestry, related.recursionAncestry]

/-- Allocation returns the same fresh identifier and related full core states. -/
theorem allocate_related (related : Related flat earlier) (node : Option Nat) :
    Results Related (allocate node flat) (EnumerationState.allocate node earlier) := by
  let nextFlat : State Symbol Guard :=
    {flat with
      counter := flat.counter + 1
      values := flat.values ++ [EnumerationState.UVarValue.unenumerated node []]
      recursionAncestry := fun other =>
        if other = flat.counter then (flat.expansionAncestry ++ flat.recursionAncestry flat.counter).eraseDups
        else flat.recursionAncestry other}
  have states : Related nextFlat (EnumerationState.allocated node earlier) := by
    refine ⟨related.valid, related.representatives, ?_, ?_, related.obligations, ?_,
      related.expansionAncestry⟩
    · change flat.counter + 1 = earlier.counter + 1
      rw [related.counter]
    · change flat.values ++ _ = earlier.values ++ _
      rw [related.values]
    · change (fun other => if other = flat.counter then _ else flat.recursionAncestry other) = _
      rw [related.counter, related.expansionAncestry, related.recursionAncestry]
      rfl
  change Results Related [.ok (flat.counter, nextFlat)]
    [.ok (earlier.counter, EnumerationState.allocated node earlier)]
  simpa only [related.counter] using
    (show Results Related [.ok (flat.counter, nextFlat)]
      [.ok (flat.counter, EnumerationState.allocated node earlier)] from .cons (.ok _ states) .nil)
