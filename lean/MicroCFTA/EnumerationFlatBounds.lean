import MicroCFTA.EnumerationFlatCore
import MicroCFTA.FlatUnionFindBounds

/-!
# Allocation-domain facts for the flat enumeration core

These facts concern actual allocation and union results. They limit explicit
forest keys separately from semantic correspondence and cached correctness.
-/

namespace MicroCFTA.EnumerationFlatState

/-- Every explicit forest entry names an allocated variable. -/
def Bounded (state : State Symbol Guard) : Prop :=
  FlatUnionFind.StoredBelow state.representatives state.counter

/-- The initial root establishes the forest allocation bound. -/
theorem initial_bounded (root : Nat) : Bounded (initial (Symbol := Symbol) (Guard := Guard) root) :=
  FlatUnionFind.initial_storedBelow [0] 1 (by simp)

/-- Actual allocation retains the forest, advances the bound and returns an absent key. -/
theorem allocate_bounded (state : State Symbol Guard) (bounded : Bounded state)
    (node : Option Nat) :
    ∃ after, allocate node state = [.ok (state.counter, after)] ∧
      after.representatives = state.representatives ∧ after.counter = state.counter + 1 ∧
      Bounded after ∧ state.representatives state.counter = none := by
  refine ⟨{state with
    counter := state.counter + 1
    values := state.values ++ [EnumerationState.UVarValue.unenumerated node []]
    recursionAncestry := fun other =>
      if other = state.counter then
        (state.expansionAncestry ++ state.recursionAncestry state.counter).eraseDups
      else state.recursionAncestry other}, rfl, rfl, rfl, ?_, bounded.fresh⟩
  change FlatUnionFind.StoredBelow state.representatives (state.counter + 1)
  exact bounded.mono (Nat.le_succ state.counter)

/-- Actual union of allocated variables retains validity and the allocation bound. -/
theorem unionVariables_bounded (state : State Symbol Guard)
    (valid : FlatUnionFind.Valid state.representatives) (bounded : Bounded state)
    (left right : Nat) (leftInside : left < state.counter) (rightInside : right < state.counter) :
    ∃ after, unionVariables left right state = [.ok ((), after)] ∧
      FlatUnionFind.Valid after.representatives ∧ Bounded after :=
  ⟨{state with representatives := FlatUnionFind.union state.representatives left right}, rfl,
    FlatUnionFind.union_valid valid left right,
    FlatUnionFind.union_storedBelow valid bounded leftInside rightInside⟩

/-- Semantic core correspondence alone does not establish an allocation bound. -/
theorem related_not_bounded :
    ∃ (flat : State Unit Unit) (earlier : EnumerationState.State Unit Unit),
      Related flat earlier ∧ ¬Bounded flat := by
  let flat : State Unit Unit :=
    ⟨1, FlatUnionFind.withInitialValues [0, 7], [.unenumerated none []], [], fun _ => [], []⟩
  let earlier : EnumerationState.State Unit Unit :=
    ⟨1, UnionFind.withInitialValues [0, 7], [.unenumerated none []], [], fun _ => [], []⟩
  refine ⟨flat, earlier, ⟨FlatUnionFind.initial_valid [0, 7],
    FlatUnionFind.initial_represents [0, 7], rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  intro bounded
  have impossible := bounded 7 (.root 1 [7]) (by simp [flat, FlatUnionFind.withInitialValues])
  change 7 < 1 at impossible
  omega

end MicroCFTA.EnumerationFlatState
