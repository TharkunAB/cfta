import MicroCFTA.EnumerationFragmentHistory

namespace MicroCFTA.EnumerationDependencies
open Fragments EnumerationState EnumerationSchedule EnumerationDriver
variable {Symbol Guard : Type}
set_option autoImplicit false

theorem pendingFragment_avoids_protected_expanded
    (before middle : State Symbol Guard) (fragment old : Fragment Symbol) (slot : Nat)
    (pending : PendingFragment middle fragment)
    (stored : before.values[slot]? = some (.enumerated old))
    (protection : EnumerationDriver.Protected slot before middle) :
    FragmentAvoid middle.representatives slot fragment := by
  intro uv hole related
  obtain ⟨pendingRoot, pendingSize, node, bucket, path, pendingStored⟩ := pending uv hole
  obtain ⟨slotSize, slotPath⟩ := protection.root
  have same : slot = pendingRoot :=
    (UnionFind.sameClass_iff_roots slotPath path).mp related
  have expandedStored : middle.values[slot]? = some (.enumerated old) :=
    protection.value.trans stored
  rw [same] at expandedStored
  cases Option.some.inj (expandedStored.symm.trans pendingStored)

end MicroCFTA.EnumerationDependencies

#check @MicroCFTA.EnumerationDependencies.pendingFragment_avoids_protected_expanded
#print axioms MicroCFTA.EnumerationDependencies.pendingFragment_avoids_protected_expanded
