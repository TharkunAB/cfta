import MicroCFTA.EnumerationState
import MicroCFTA.UnionFindSupport

namespace MicroCFTA.EnumerationStateAllocation

open UnionFindSupport

variable {Symbol Guard : Type}

/-- Inheriting ancestry preserves the allocation and representative fields. -/
theorem inheritAncestry_frame (state : EnumerationState.State Symbol Guard) (key : Nat) :
    ∃ after,
      EnumerationState.inheritAncestry key state = [Except.ok ((), after)] ∧
      after.counter = state.counter ∧
      after.representatives = state.representatives ∧
      after.values = state.values ∧
      after.obligations = state.obligations ∧
      after.expansionAncestry = state.expansionAncestry := by
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Allocation returns the old counter and adds one value slot. -/
theorem allocate_frame (state : EnumerationState.State Symbol Guard) (node : Option Nat) :
    ∃ after,
      EnumerationState.allocate node state = [Except.ok (state.counter, after)] ∧
      after.counter = state.counter + 1 ∧
      after.values.length = state.values.length + 1 ∧
      after.representatives = state.representatives ∧
      after.obligations = state.obligations ∧
      after.expansionAncestry = state.expansionAncestry := by
  refine ⟨_, rfl, rfl, ?_, rfl, rfl, rfl⟩
  simp

/-- Allocation preserves the internal bounds at the new counter. -/
theorem allocate_preserves_invariants
    (state : EnumerationState.State Symbol Guard) (node : Option Nat)
    (shape : state.values.length = state.counter)
    (supported : SupportedBelow state.counter state.representatives)
    (parents : ParentsBelow state.counter state.representatives)
    (total : UnionFind.Total state.representatives) :
    ∃ after,
      EnumerationState.allocate node state = [Except.ok (state.counter, after)] ∧
      after.counter = state.counter + 1 ∧
      state.counter < after.counter ∧
      after.values.length = after.counter ∧
      SupportedBelow after.counter after.representatives ∧
      ParentsBelow after.counter after.representatives ∧
      UnionFind.Total after.representatives := by
  obtain ⟨after, run, counter, length, forest, _, _⟩ := allocate_frame state node
  refine ⟨after, run, counter, ?_, ?_, ?_, ?_, ?_⟩
  · rw [counter]
    exact Nat.lt_succ_self _
  · rw [length, counter, shape]
  · rw [forest, counter]
    exact supportedBelow_mono supported (Nat.le_succ _)
  · rw [forest, counter]
    exact parentsBelow_mono parents (Nat.le_succ _)
  · rw [forest]
    exact total

/-- Initialization establishes the counter, value count, and forest invariants. -/
theorem initial_invariants (root : Nat) :
    let state : EnumerationState.State Symbol Guard := EnumerationState.initial root
    state.counter = 1 ∧
      state.values.length = state.counter ∧
      SupportedBelow state.counter state.representatives ∧
      ParentsBelow state.counter state.representatives ∧
      UnionFind.Total state.representatives := by
  dsimp
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · simpa [EnumerationState.initial, initialBound] using
      (supportedBelow_withInitialValues [0])
  · simpa [EnumerationState.initial, initialBound] using
      (parentsBelow_withInitialValues [0])
  · intro key
    refine ⟨key, 1, UnionFind.Reaches.root ?_⟩
    by_cases zero : key = 0
    · subst key
      simp [EnumerationState.initial, MicroCFTA.UnionFind.read,
        UnionFind.withInitialValues]
    · simp [EnumerationState.initial, MicroCFTA.UnionFind.read,
        UnionFind.withInitialValues, zero]

end MicroCFTA.EnumerationStateAllocation
