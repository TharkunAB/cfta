import MicroCFTA.EnumerationReferences

/-!
# Pending targets of returned fragment holes

Returned holes resolve to pending slots. Later pending-class operations
retain this fact when they protect every earlier expanded class.
-/
namespace MicroCFTA.EnumerationDependencies
open Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver

/-- Every hole resolves to a pending slot in the actual state. -/
def PendingFragment (state : State Symbol Guard) (fragment : Fragment Symbol) : Prop :=
  ∀ uv, HasHole fragment uv → ∃ root size node scs,
    UnionFind.Reaches state.representatives uv root size ∧
      state.values[root]? = some (.unenumerated node scs)

/-- A hole with an actual pending-root receipt has a pending target. -/
theorem pendingFragment_hole (state : State Symbol Guard) (uv root size : Nat)
    (node : Option Nat) (scs : List Suspended)
    (path : UnionFind.Reaches state.representatives uv root size)
    (stored : state.values[root]? = some (.unenumerated node scs)) :
    PendingFragment state (.hole uv) := by
  intro other hole
  cases hole
  exact ⟨root, size, node, scs, path, stored⟩

/-- A concrete fragment retains the pending targets of every child. -/
theorem pendingFragment_node (state : State Symbol Guard) (symbol : Symbol)
    (children : List (Fragment Symbol))
    (pending : ∀ child ∈ children, PendingFragment state child) :
    PendingFragment state (.node symbol children) := by
  intro uv hole
  cases hole with
  | child _ _ child _ member below => exact pending child member uv below

/-- Safe later storage retains pending targets through protected earlier expanded classes. -/
theorem pendingFragment_preserved (before after : State Symbol Guard)
    (beforeSafe : Safe before) (afterSafe : Safe after)
    (growth : before.counter ≤ after.counter) (fragment : Fragment Symbol)
    (allocated : FragmentBound before.counter fragment) (pending : PendingFragment before fragment)
    (origin : EnumeratedOrigin before after)
    (protects : ∀ held storedFragment, before.values[held]? = some (.enumerated storedFragment) →
      Protected held before after) : PendingFragment after fragment := by
  intro uv hole
  have inside := Nat.lt_of_lt_of_le (hasHole_bounded before.counter fragment uv allocated hole) growth
  obtain ⟨root, size, path⟩ := afterSafe.1.total uv
  have rootInside := reaches_bounded after.representatives after.counter afterSafe.1.forest path inside
  have index : root < after.values.length := by rw [← afterSafe.1.aligned]; exact rootInside
  let value := after.values[root]
  have stored : after.values[root]? = some value := List.getElem?_eq_getElem index
  have live : value ≠ .eliminated :=
    (afterSafe.2 root value stored).mpr ⟨size, .root (UnionFind.reaches_terminal path)⟩
  cases valueEq : value with
  | eliminated => exact (live valueEq).elim
  | unenumerated node scs =>
      exact ⟨root, size, node, scs, path, by simpa [valueEq] using stored⟩
  | enumerated storedFragment =>
      have afterStored : after.values[root]? = some (.enumerated storedFragment) := by
        simpa [valueEq] using stored
      have beforeStored := origin root storedFragment afterStored
      have frame := protects root storedFragment beforeStored
      have related := (frame.classes uv).mp (UnionFind.sameClass_symm (UnionFind.sameClass_root path))
      obtain ⟨rootSize, rootPath⟩ := (enumerated_root before beforeSafe root storedFragment beforeStored).2
      obtain ⟨pendingRoot, pendingSize, node, scs, pendingPath, pendingStored⟩ := pending uv hole
      have same := (UnionFind.sameClass_iff_roots rootPath pendingPath).mp related
      rw [same] at beforeStored
      cases Option.some.inj (beforeStored.symm.trans pendingStored)

/-- Writing a separate target retains every pending target of the stored fragment. -/
theorem pendingFragment_write (before : State Symbol Guard) (target : Nat)
    (fragment : Fragment Symbol) (pending : PendingFragment before fragment)
    (separate : FragmentAvoid before.representatives target fragment) :
    PendingFragment {before with values := before.values.set target (.enumerated fragment)} fragment := by
  intro uv hole
  obtain ⟨root, size, node, scs, path, stored⟩ := pending uv hole
  have different : root ≠ target := by
    intro same
    subst root
    exact separate uv hole (UnionFind.sameClass_symm (UnionFind.sameClass_root path))
  refine ⟨root, size, node, scs, path, ?_⟩
  change (before.values.set target (.enumerated fragment))[root]? = some (.unenumerated node scs)
  rw [List.getElem?_set_ne (Ne.symm different)]
  exact stored

end MicroCFTA.EnumerationDependencies
