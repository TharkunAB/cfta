import MicroCFTA.EnumerationFlatCore

/-!
# Raw-slot assimilation with direct-parent union-find

The worker retains the earlier core order: read the raw source, skip an
eliminated source, check the intersection, then update both raw slots and
ancestry. Native intersection and index effects remain separate interfaces.
-/

namespace MicroCFTA.EnumerationFlatState

open EnumerationResultRelation (Results)
open EnumerationState (Graph UVarValue Suspended intersectValues hasEmptyContents)

variable {Symbol Guard : Type} {flat : State Symbol Guard}
  {earlier : EnumerationState.State Symbol Guard}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Move a recorded raw source slot into the selected target slot. -/
def assimilate (graph : Graph Symbol Guard) (target source : Nat) : Action Symbol Guard Unit := do
  if target = source then pure () else
    let sourceValue ← rawValue source
    match sourceValue with
    | .eliminated => pure ()
    | _ =>
      let targetValue ← rawValue target
      match intersectValues graph sourceValue targetValue with
      | none => failure .invalidIntersection
      | some merged =>
        require (!hasEmptyContents graph merged)
        setValue target merged
        setValue source .eliminated
        modify fun state => {state with recursionAncestry := (fun other =>
          if other = target then
            (state.recursionAncestry source ++ state.recursionAncestry target).eraseDups
          else state.recursionAncestry other)}

/-- Assimilation retains every ordered core result, rejection and explicit error. -/
theorem assimilate_related (related : Related flat earlier) (graph : Graph Symbol Guard)
    (target source : Nat) :
    Results Related (assimilate graph target source flat)
      (EnumerationState.assimilate graph target source earlier) := by
  unfold assimilate EnumerationState.assimilate
  by_cases same : target = source
  · simp only [same, ↓reduceIte]
    exact pure_related related ()
  · simp only [same, ↓reduceIte]
    apply EnumerationResultRelation.stateT_bind _ _ _ _ (rawValue_related related source)
    intro sourceValue left right states
    cases sourceValue
    case eliminated => exact pure_related states ()
    all_goals
      apply EnumerationResultRelation.stateT_bind _ _ _ _ (rawValue_related states target)
      intro targetValue left right states
      split
      · exact failure_related .invalidIntersection
      · rename_i merged _
        apply EnumerationResultRelation.stateT_bind _ _ _ _
          (require_related states (!hasEmptyContents graph merged))
        intro _ left right states
        apply EnumerationResultRelation.stateT_bind _ _ _ _ (setValue_related states target merged)
        intro _ left right states
        apply EnumerationResultRelation.stateT_bind _ _ _ _ (setValue_related states source .eliminated)
        intro _ left right states
        change Results Related
          [.ok ((), {left with recursionAncestry := fun other =>
            if other = target then (left.recursionAncestry source ++ left.recursionAncestry target).eraseDups
            else left.recursionAncestry other})]
          [.ok ((), {right with recursionAncestry := fun other =>
            if other = target then (right.recursionAncestry source ++ right.recursionAncestry target).eraseDups
            else right.recursionAncestry other})]
        refine .cons (.ok () ⟨states.valid, states.representatives, states.counter,
          states.values, states.obligations, ?_, states.expansionAncestry⟩) .nil
        rw [states.recursionAncestry]

/-- Merge an incoming node at the actual representative before the emptiness guard. -/
def mergeNode (graph : Graph Symbol Guard) (uv node : Nat) (scs : List Suspended) :
    Action Symbol Guard Unit := do
  let target ← representative uv
  let previous ← rawValue target
  match intersectValues graph (.unenumerated (some node) scs) previous with
  | none => failure .invalidIntersection
  | some merged =>
    setValue target merged
    inheritAncestry target
    require (!hasEmptyContents graph merged)

/-- Incoming-node merging keeps the actual resolved target and every core outcome. -/
theorem mergeNode_related (related : Related flat earlier) (graph : Graph Symbol Guard)
    (completed : UnionFind.findRoot fuel earlier.representatives uv = some found)
    (node : Nat) (scs : List Suspended) :
    Results Related (mergeNode graph uv node scs flat)
      (EnumerationState.mergeNode graph fuel uv node scs earlier) := by
  unfold mergeNode EnumerationState.mergeNode
  apply EnumerationResultRelation.stateT_bind _ _ _ _ (representative_related related completed)
  intro target left right states
  apply EnumerationResultRelation.stateT_bind _ _ _ _ (rawValue_related states target)
  intro previous left right states
  split
  · exact failure_related .invalidIntersection
  · rename_i merged _
    apply EnumerationResultRelation.stateT_bind _ _ _ _ (setValue_related states target merged)
    intro _ left right states
    apply EnumerationResultRelation.stateT_bind _ _ _ _ (inheritAncestry_related states target)
    intro _ left right states
    exact require_related states (!hasEmptyContents graph merged)

/-- Incoming-node merging agrees at one sufficient earlier bound and every extension. -/
theorem mergeNode_stable (related : Related flat earlier) (graph : Graph Symbol Guard)
    (uv node : Nat) (scs : List Suspended) :
    ∃ fuel, ∀ extra, Results Related (mergeNode graph uv node scs flat)
      (EnumerationState.mergeNode graph (fuel + extra) uv node scs earlier) := by
  obtain ⟨fuel, found, stable, _, _, _⟩ := FlatUnionFind.find_stable related.representatives uv
  exact ⟨fuel, fun extra => mergeNode_related related graph (stable extra) node scs⟩

end MicroCFTA.EnumerationFlatState
