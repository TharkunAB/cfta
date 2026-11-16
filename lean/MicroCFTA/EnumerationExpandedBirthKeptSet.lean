import MicroCFTA.EnumerationExpandedBirthHistory

namespace MicroCFTA.EnumerationDependencies
open Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
variable {Symbol Guard : Type}
set_option autoImplicit false

/-- Retain classes outside every original expanded class and the held class. -/
def ExpandedBirthKept (before after : State Symbol Guard) (held uv : Nat) : Prop :=
  (¬∃ (old : Nat) (oldFragment : Fragment Symbol),
    before.values[old]? = some (.enumerated oldFragment) ∧
      UnionFind.SameClass after.representatives old uv) ∧
  ¬UnionFind.SameClass after.representatives held uv

/-- Actual birth origins close the retained set under every stored raw hole. -/
theorem expanded_birth_kept_dependencies
    (before after : State Symbol Guard) (held : Nat)
    (roots : Nat → Nat) (paths : Roots after.representatives roots)
    (births : ExpandedBirthHistory before after)
    (heldOrigin : ∀ (slot : Nat) (fragment : Fragment Symbol),
      after.values[slot]? = some (.enumerated fragment) →
      before.values[slot]? = some (.enumerated fragment) ∨
        FragmentAvoid after.representatives held fragment) :
    ∀ uv, ExpandedBirthKept before after held uv → ∀ fragment,
      after.values[roots uv]? = some (.enumerated fragment) →
      ∀ hole, HasHole fragment hole → ExpandedBirthKept before after held hole := by
  intro uv supported fragment stored hole present
  obtain ⟨_, path⟩ := paths uv
  have related : UnionFind.SameClass after.representatives (roots uv) uv :=
    UnionFind.sameClass_symm (UnionFind.sameClass_root path)
  have notOriginal : before.values[roots uv]? ≠ some (.enumerated fragment) := by
    intro old
    exact supported.1 ⟨roots uv, fragment, old, related⟩
  rcases births.2 (roots uv) fragment stored with old | born
  · exact (notOriginal old).elim
  · rcases heldOrigin (roots uv) fragment stored with old | heldAvoid
    · exact (notOriginal old).elim
    · refine ⟨?_, heldAvoid hole present⟩
      rintro ⟨old, oldFragment, oldStored, same⟩
      exact born old oldFragment oldStored hole present same

/-- Genuine pending inputs retain their raw aliases in the kept set. -/
theorem expanded_birth_kept_inputs
    (before after : State Symbol Guard) (held : Nat) (bucket : List Suspended)
    (births : ExpandedBirthHistory before after)
    (pending : InputsPending before bucket)
    (heldSeparate : Avoids after.representatives held bucket) :
    ∀ sc ∈ bucket, ExpandedBirthKept before after held sc.var := by
  intro sc member
  refine ⟨?_, heldSeparate sc member⟩
  rintro ⟨old, oldFragment, oldStored, joined⟩
  have beforeJoined : UnionFind.SameClass before.representatives old sc.var :=
    ((births.1 old oldFragment oldStored).classes sc.var).mp joined
  exact pending old oldFragment oldStored sc member beforeJoined

end MicroCFTA.EnumerationDependencies
