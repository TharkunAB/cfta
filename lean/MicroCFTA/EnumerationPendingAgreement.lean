import MicroCFTA.EnumerationReferences

/-!
# Agreement on actual stored suspended references

Safe storage bounds each raw reference. Its representative is live.
PendingReferences excludes an expanded representative for a stored reference.
Agreement on pending roots therefore includes eliminated raw aliases.
-/

namespace MicroCFTA.EnumerationPendingAgreement
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver
open EnumerationDependencies EnumerationReferences

variable {Symbol Guard : Type}

/-- Direct pending-slot agreement includes every raw target in a stored pending bucket. -/
theorem stored_suspended_target_agreement
    (state : State Symbol Guard) (safe : Safe state) (pending : PendingReferences state)
    (left right : Nat → Term Symbol)
    (leftAliases : UnionFind.Satisfies state.representatives left)
    (rightAliases : UnionFind.Satisfies state.representatives right)
    (agree : ∀ uv node scs, state.values[uv]? = some (.unenumerated node scs) → left uv = right uv)
    (owner : Nat) (node : Option Nat) (bucket : List Suspended)
    (stored : state.values[owner]? = some (.unenumerated node bucket))
    (sc : Suspended) (member : sc ∈ bucket) : left sc.var = right sc.var := by
  have inside : sc.var < state.counter :=
    safe.1.values (.unenumerated node bucket) (List.mem_of_getElem? stored) sc member
  obtain ⟨root, size, path⟩ := safe.1.total sc.var
  have rootInside := reaches_bounded state.representatives state.counter safe.1.forest path inside
  have index : root < state.values.length := by
    rw [← safe.1.aligned]
    exact rootInside
  let value := state.values[root]
  have rootStored : state.values[root]? = some value := List.getElem?_eq_getElem index
  have live : value ≠ .eliminated :=
    (safe.2 root value rootStored).mpr ⟨size, .root (UnionFind.reaches_terminal path)⟩
  have same := UnionFind.sameClass_root path
  cases valueEq : value with
  | eliminated => exact (live valueEq).elim
  | unenumerated pendingNode pendingScs =>
      have rootPending : state.values[root]? = some (.unenumerated pendingNode pendingScs) := by
        simpa only [valueEq] using rootStored
      exact (leftAliases sc.var root same).trans
        ((agree root pendingNode pendingScs rootPending).trans (rightAliases sc.var root same).symm)
  | enumerated fragment =>
      have rootExpanded : state.values[root]? = some (.enumerated fragment) := by
        simpa only [valueEq] using rootStored
      have avoids := pending_inputs state pending owner node bucket stored root fragment rootExpanded
      exact (avoids sc member (UnionFind.sameClass_symm same)).elim

/-- One pending owner's full stored bucket retains every Holds predicate under the same assignment extension. -/
theorem stored_bucket_holds_transfer
    (state : State Symbol Guard) (safe : Safe state) (pending : PendingReferences state)
    (left right : Nat → Term Symbol)
    (leftAliases : UnionFind.Satisfies state.representatives left)
    (rightAliases : UnionFind.Satisfies state.representatives right)
    (agree : ∀ uv node scs, state.values[uv]? = some (.unenumerated node scs) → left uv = right uv)
    (owner : Nat) (node : Option Nat) (bucket : List Suspended)
    (stored : state.values[owner]? = some (.unenumerated node bucket))
    (holds : ∀ sc ∈ bucket, Suspended.Holds left (left owner) sc) :
    ∀ sc ∈ bucket, Suspended.Holds right (right owner) sc := by
  have ownerSame := agree owner node bucket stored
  intro sc member path represented
  have targetSame := stored_suspended_target_agreement state safe pending left right
    leftAliases rightAliases agree owner node bucket stored sc member
  simpa only [ownerSame, targetSame] using holds sc member path represented

end MicroCFTA.EnumerationPendingAgreement
