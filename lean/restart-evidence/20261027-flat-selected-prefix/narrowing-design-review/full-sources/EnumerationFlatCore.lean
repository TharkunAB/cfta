import MicroCFTA.EnumerationFlatPrimitives

/-!
# Representative access and allocation in the flat enumeration core

The correspondence composes actual StateT transitions. It keeps invalid-slot
errors and relates complete successful core states at sufficient old bounds.
-/

namespace MicroCFTA.EnumerationFlatState

open EnumerationResultRelation (Results)

variable {Symbol Guard α : Type} {flat : State Symbol Guard}
  {earlier : EnumerationState.State Symbol Guard}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Returning a common value retains the related input states. -/
theorem pure_related (related : Related flat earlier) (value : α) :
    Results Related ((pure value : Action Symbol Guard α) flat)
      ((pure value : EnumerationState.EnumerateM Symbol Guard α) earlier) :=
  .cons (.ok value related) .nil

/-- Rejection contributes no result on either side. -/
theorem reject_related : Results Related (reject (α := α) flat)
    (EnumerationState.reject earlier) := .nil

/-- An explicit error has the same identity and position on both sides. -/
theorem failure_related (error : EnumerationState.Error) :
    Results Related (failure (α := α) error flat) (EnumerationState.failure error earlier) :=
  .cons (.error error) .nil

/-- The same Boolean guard either preserves the states or rejects both branches. -/
theorem require_related (related : Related flat earlier) (condition : Bool) :
    Results Related (require condition flat) (EnumerationState.require condition earlier) := by
  cases condition
  · exact .nil
  · exact pure_related related ()

/-- Representative-slot access keeps equal values and identical invalid-slot errors. -/
theorem getValue_related (related : Related flat earlier)
    (completed : UnionFind.findRoot fuel earlier.representatives uv = some found) :
    Results Related (getValue uv flat) (EnumerationState.getValue fuel uv earlier) := by
  unfold getValue EnumerationState.getValue
  apply EnumerationResultRelation.stateT_bind _ _ _ _ (representative_related related completed)
  intro value left right states
  exact rawValue_related states value

/-- Representative-slot access has a genuine stable sufficient earlier bound. -/
theorem getValue_stable (related : Related flat earlier) (uv : Nat) :
    ∃ fuel, ∀ extra, Results Related (getValue uv flat)
      (EnumerationState.getValue (fuel + extra) uv earlier) := by
  obtain ⟨fuel, found, stable, _, _, _⟩ := FlatUnionFind.find_stable related.representatives uv
  exact ⟨fuel, fun extra => getValue_related related (stable extra)⟩

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

end MicroCFTA.EnumerationFlatState
