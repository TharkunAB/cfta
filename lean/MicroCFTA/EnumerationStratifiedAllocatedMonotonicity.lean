import MicroCFTA.EnumerationStratifiedTransport

namespace MicroCFTA.EnumerationOrder
open Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationDriver EnumerationDependencies
variable {Symbol Guard : Type}
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Transport does not decrease the level of an old allocated raw variable. -/
theorem stratified_transport_allocated_nondecreasing
    (before after : State Symbol Guard) (beforeSafe : Safe before) (afterSafe : Safe after)
    (growth : before.counter ≤ after.counter) (level nextLevel : Nat → Nat) (frontier : Nat)
    (beforeOrder : Stratified before level frontier) (afterOrder : Stratified after nextLevel frontier)
    (origin : EnumeratedOrigin before after)
    (protects : ∀ slot fragment, before.values[slot]? = some (.enumerated fragment) →
      Protected slot before after)
    (fixedOld : ∀ slot fragment, before.values[slot]? = some (.enumerated fragment) →
      nextLevel slot = level slot) :
    ∀ uv, uv < before.counter → level uv ≤ nextLevel uv := by
  have oldBound : ∀ uv, uv < before.counter → level uv ≤ frontier := by
    intro uv inside
    obtain ⟨root, size, path⟩ := beforeSafe.1.total uv
    have rootInside := reaches_bounded before.representatives before.counter
      beforeSafe.1.forest path inside
    have index : root < before.values.length := by
      rw [← beforeSafe.1.aligned]
      exact rootInside
    let value := before.values[root]
    have stored : before.values[root]? = some value := List.getElem?_eq_getElem index
    have live : value ≠ .eliminated :=
      (beforeSafe.2 root value stored).mpr ⟨size, .root (UnionFind.reaches_terminal path)⟩
    have same := UnionFind.sameClass_root path
    cases valueEq : value with
    | eliminated => exact (live valueEq).elim
    | unenumerated node scs =>
        have pending : before.values[root]? = some (.unenumerated node scs) := by
          simpa only [valueEq] using stored
        exact Nat.le_of_eq ((beforeOrder.classes uv root same).trans
          (beforeOrder.pending root node scs pending))
    | enumerated fragment =>
        have expanded : before.values[root]? = some (.enumerated fragment) := by
          simpa only [valueEq] using stored
        calc
          level uv = level root := beforeOrder.classes uv root same
          _ ≤ frontier := Nat.le_of_lt (beforeOrder.expanded root fragment expanded).1
  intro uv inside
  obtain ⟨root, size, path⟩ := afterSafe.1.total uv
  have rootInside := reaches_bounded after.representatives after.counter
    afterSafe.1.forest path (Nat.lt_of_lt_of_le inside growth)
  have index : root < after.values.length := by
    rw [← afterSafe.1.aligned]
    exact rootInside
  let value := after.values[root]
  have stored : after.values[root]? = some value := List.getElem?_eq_getElem index
  have live : value ≠ .eliminated :=
    (afterSafe.2 root value stored).mpr ⟨size, .root (UnionFind.reaches_terminal path)⟩
  have same := UnionFind.sameClass_root path
  cases valueEq : value with
  | eliminated => exact (live valueEq).elim
  | unenumerated node scs =>
      have pending : after.values[root]? = some (.unenumerated node scs) := by
        simpa only [valueEq] using stored
      have currentLevel : nextLevel uv = frontier :=
        (afterOrder.classes uv root same).trans (afterOrder.pending root node scs pending)
      calc
        level uv ≤ frontier := oldBound uv inside
        _ = nextLevel uv := currentLevel.symm
  | enumerated fragment =>
      have expanded : after.values[root]? = some (.enumerated fragment) := by
        simpa only [valueEq] using stored
      have original := origin root fragment expanded
      have retained := protects root fragment original
      have oldRelated := (retained.classes uv).mp (UnionFind.sameClass_symm same)
      have oldLevel : level uv = level root := (beforeOrder.classes root uv oldRelated).symm
      have currentLevel : nextLevel uv = nextLevel root := afterOrder.classes uv root same
      exact Nat.le_of_eq (oldLevel.trans ((fixedOld root fragment original).symm.trans currentLevel.symm))

end MicroCFTA.EnumerationOrder
