import MicroCFTA.EnumerationPendingAssignmentCongruence
import MicroCFTA.EnumerationPendingAssignmentFixedPoint
import MicroCFTA.EnumerationPendingEvaluationWitness

namespace MicroCFTA.EnumerationPendingAssignment
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver
open EnumerationDependencies EnumerationOrder
variable {Symbol Guard : Type}
set_option autoImplicit false

/-- A retained level cut and actual fragment origins give a dependency-closed set. -/
theorem dependency_closed_above_cut
    (before after : State Symbol Guard) (roots : Nat → Nat)
    (paths : Roots after.representatives roots)
    (level : Nat → Nat) (frontier held cut : Nat)
    (stratified : Stratified after level frontier)
    (origin : ∀ (slot : Nat) (fragment : Fragment Symbol), after.values[slot]? = some (.enumerated fragment) →
      before.values[slot]? = some (.enumerated fragment) ∨
        FragmentAvoid after.representatives held fragment)
    (oldBelow : ∀ (slot : Nat) (fragment : Fragment Symbol), before.values[slot]? = some (.enumerated fragment) → level slot < cut) :
    ∀ uv, (cut ≤ level uv ∧ ¬UnionFind.SameClass after.representatives held uv) →
      ∀ fragment, after.values[roots uv]? = some (.enumerated fragment) →
        ∀ hole, HasHole fragment hole →
          cut ≤ level hole ∧ ¬UnionFind.SameClass after.representatives held hole
 := by
  intro uv kept fragment stored hole present
  obtain ⟨size, path⟩ := paths uv
  have sameLevel := stratified.classes uv (roots uv) (UnionFind.sameClass_root path)
  have rootAbove : cut ≤ level (roots uv) := sameLevel ▸ kept.1
  rcases origin (roots uv) fragment stored with old | separate
  · have below := oldBelow (roots uv) fragment old
    omega
  · have higher := (stratified.expanded (roots uv) fragment stored).2 hole present
    exact ⟨Nat.le_of_lt (Nat.lt_of_le_of_lt rootAbove higher), separate hole present⟩

/-- One explicit finite assignment restores stored equations and keeps every supported value. -/
theorem recomplete_with_base_on
    (state : State Symbol Guard) (safe : Safe state)
    (roots : Nat → Nat) (paths : Roots state.representatives roots)
    (level : Nat → Nat) (frontier : Nat) (stratified : Stratified state level frontier)
    (current base : Nat → Term Symbol)
    (currentAliases : UnionFind.Satisfies state.representatives current)
    (currentEquations : ∀ slot fragment, state.values[slot]? = some (.enumerated fragment) →
      fill current fragment = current slot)
    (baseAliases : UnionFind.Satisfies state.representatives base)
    (kept : Nat → Prop)
    (dependencies : ∀ uv, kept uv → ∀ fragment,
      state.values[roots uv]? = some (.enumerated fragment) →
      ∀ hole, HasHole fragment hole → kept hole)
    (agree : ∀ uv, kept uv → base uv = current uv) :
    let updated := evaluateSlotsWith state.values roots base (frontier + 1)
    UnionFind.Satisfies state.representatives updated ∧
      (∀ uv fragment, state.values[uv]? = some (.enumerated fragment) →
        updated uv = fill updated fragment) ∧
      (∀ uv node bucket, state.values[uv]? = some (.unenumerated node bucket) → updated uv = base uv) ∧
      ∀ uv, kept uv → updated uv = current uv
 := by
  dsimp only
  obtain ⟨aliases, equations, pending⟩ :=
    evaluateSlotsWith_witness state safe roots paths level frontier stratified base baseAliases
  refine ⟨aliases, equations, pending, ?_⟩
  intro uv supported
  have sameEvaluation := evaluateSlotsWith_congr_on state.values roots base current kept
    dependencies agree (frontier + 1) uv supported
  exact sameEvaluation.trans
    (evaluateSlotsWith_fixed_of_stored_equations state roots paths current
      currentAliases currentEquations (frontier + 1) uv)

end MicroCFTA.EnumerationPendingAssignment
