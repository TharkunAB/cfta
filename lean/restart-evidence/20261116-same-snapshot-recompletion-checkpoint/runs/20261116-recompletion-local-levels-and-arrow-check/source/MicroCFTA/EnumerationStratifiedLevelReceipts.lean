import MicroCFTA.EnumerationStratifiedTransport

namespace MicroCFTA.EnumerationOrder
open Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationDriver EnumerationDependencies
variable {Symbol Guard : Type}
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Retain old expanded levels and the frontier for old pending slots. -/
theorem stratified_preserved_with_old_levels
    (before after : State Symbol Guard) (beforeSafe : Safe before) (afterSafe : Safe after)
    (level : Nat → Nat) (frontier : Nat)
    (stratified : Stratified before level frontier) (origin : EnumeratedOrigin before after)
    (protects : ∀ slot fragment, before.values[slot]? = some (.enumerated fragment) →
      Protected slot before after) :
    ∃ nextLevel, Stratified after nextLevel frontier ∧
      (∀ slot fragment, before.values[slot]? = some (.enumerated fragment) →
        nextLevel slot = level slot) ∧
      (∀ slot node scs, before.values[slot]? = some (.unenumerated node scs) →
        nextLevel slot = frontier) := by
  obtain ⟨roots, paths⟩ := roots_exist after.representatives afterSafe.1.total
  let nextLevel := fun uv => match after.values[roots uv]? with
    | some (.enumerated _) => level (roots uv)
    | _ => frontier
  have fixedExpanded : ∀ uv storedFragment,
      after.values[uv]? = some (.enumerated storedFragment) → nextLevel uv = level uv := by
    intro uv storedFragment stored
    have fixed := stored_root_fixed after afterSafe roots paths uv _ stored (by simp)
    simp [nextLevel, fixed, stored]
  have nextOrder : Stratified after nextLevel frontier := by
    refine ⟨?_, ?_, ?_⟩
    · intro left right same
      have sameRoot := (class_iff after.representatives roots paths left right).mp same
      simp [nextLevel, sameRoot]
    · intro uv storedFragment stored
      rw [fixedExpanded uv storedFragment stored]
      have beforeStored := origin uv storedFragment stored
      obtain ⟨bound, dependencies⟩ := stratified.expanded uv storedFragment beforeStored
      refine ⟨bound, ?_⟩
      intro hole present
      have oldDependency := dependencies hole present
      cases target : after.values[roots hole]? with
      | none => simpa [nextLevel, target] using bound
      | some value =>
          cases value with
          | eliminated | unenumerated _ _ => simpa [nextLevel, target] using bound
          | enumerated targetFragment =>
              have beforeTarget := origin (roots hole) targetFragment target
              have frame := protects (roots hole) targetFragment beforeTarget
              obtain ⟨size, path⟩ := paths hole
              have related := (frame.classes hole).mp
                (UnionFind.sameClass_symm (UnionFind.sameClass_root path))
              have sameLevel := stratified.classes (roots hole) hole related
              simpa [nextLevel, target, sameLevel] using oldDependency
    · intro uv node scs stored
      have fixed := stored_root_fixed after afterSafe roots paths uv _ stored (by simp)
      simp [nextLevel, fixed, stored]
  refine ⟨nextLevel, nextOrder, ?_, ?_⟩
  · intro slot fragment stored
    exact fixedExpanded slot fragment ((protects slot fragment stored).value.trans stored)
  · intro slot node scs stored
    have slotRoot : IsRoot before.representatives slot :=
      (beforeSafe.2 slot (.unenumerated node scs) stored).mp (by simp)
    cases target : after.values[roots slot]? with
    | none => simp [nextLevel, target]
    | some value =>
        cases value with
        | eliminated | unenumerated _ _ => simp [nextLevel, target]
        | enumerated old =>
            have original := origin (roots slot) old target
            have retained := protects (roots slot) old original
            obtain ⟨size, path⟩ := paths slot
            have related := (retained.classes slot).mp
              (UnionFind.sameClass_symm (UnionFind.sameClass_root path))
            have expandedRoot := (enumerated_root before beforeSafe (roots slot) old original).2
            have equal : roots slot = slot :=
              (UnionFind.sameClass_iff_roots expandedRoot.choose_spec slotRoot.choose_spec).mp related
            rw [equal] at original
            cases Option.some.inj (original.symm.trans stored)

/-- Retain pointwise level growth and old expanded levels at the same write. -/
theorem write_stratified_with_old_levels
    (before : State Symbol Guard) (safe : Safe before)
    (level : Nat → Nat) (frontier uv : Nat)
    (stratified : Stratified before level frontier) (node : Option Nat) (scs : List Suspended)
    (stored : before.values[uv]? = some (.unenumerated node scs)) (fragment : Fragment Symbol)
    (pendingHoles : ∀ hole, HasHole fragment hole → ∃ root size node scs,
      UnionFind.Reaches before.representatives hole root size ∧
        before.values[root]? = some (.unenumerated node scs))
    (separate : FragmentAvoid before.representatives uv fragment) :
    ∃ nextLevel,
      Stratified {before with values := before.values.set uv (.enumerated fragment)}
        nextLevel (frontier + 1) ∧
      (∀ index, level index ≤ nextLevel index) ∧
      (∀ index old, before.values[index]? = some (.enumerated old) →
        nextLevel index = level index) := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives safe.1.total
  have fixed := stored_root_fixed before safe roots paths uv _ stored (by simp)
  have selectedLevel := stratified.pending uv node scs stored
  let nextLevel := fun index => if roots index = uv then frontier else if level index = frontier then frontier + 1 else level index
  have sameRootLevel : ∀ index, roots index = uv → level index = frontier := by
    intro index selected
    obtain ⟨size, path⟩ := paths index
    have same := stratified.classes index (roots index) (UnionFind.sameClass_root path)
    simpa [selected, selectedLevel] using same
  have increases : ∀ index, level index ≤ nextLevel index := by
    intro index
    by_cases selected : roots index = uv
    · simp [nextLevel, selected, sameRootLevel index selected]
    · by_cases atFrontier : level index = frontier <;> simp [nextLevel, selected, atFrontier]
  have selectedNext : nextLevel uv = frontier := by simp [nextLevel, fixed]
  have oldExpanded : ∀ index storedFragment, before.values[index]? = some (.enumerated storedFragment) → nextLevel index = level index := by
    intro index storedFragment old
    have bound := (stratified.expanded index storedFragment old).1
    have notSelected : roots index ≠ uv := by intro same; have equal := sameRootLevel index same; omega
    have notFrontier : level index ≠ frontier := by omega
    simp [nextLevel, notSelected, notFrontier]
  have nextOrder : Stratified {before with values := before.values.set uv (.enumerated fragment)}
      nextLevel (frontier + 1) := by
    refine ⟨?_, ?_, ?_⟩
    · intro left right same
      have sameRoot := (class_iff before.representatives roots paths left right).mp same
      have sameLevel := stratified.classes left right same
      simp [nextLevel, sameRoot, sameLevel]
    · intro index storedFragment read
      by_cases selected : index = uv
      · subst index
        have inside := (List.getElem?_eq_some_iff.mp stored).1
        have fragmentSame : storedFragment = fragment := by simpa [inside] using read.symm
        subst storedFragment
        rw [selectedNext]
        refine ⟨by omega, ?_⟩
        intro hole present
        obtain ⟨root, size, node, scs, path, pendingRead⟩ := pendingHoles hole present
        have holeLevel := (stratified.classes hole root (UnionFind.sameClass_root path)).trans (stratified.pending root node scs pendingRead)
        have different : roots hole ≠ uv := by
          intro same
          apply separate hole present
          exact (class_iff before.representatives roots paths uv hole).mpr (fixed.trans same.symm)
        simp [nextLevel, different, holeLevel]
      · have old : before.values[index]? = some (.enumerated storedFragment) := by simpa [Ne.symm selected] using read
        obtain ⟨bound, dependencies⟩ := stratified.expanded index storedFragment old
        rw [oldExpanded index storedFragment old]
        exact ⟨by omega, fun hole present => Nat.lt_of_lt_of_le (dependencies hole present) (increases hole)⟩
    · intro index pendingNode pendingScs read
      have notSelected : index ≠ uv := by
        intro same
        subst index
        have inside := (List.getElem?_eq_some_iff.mp stored).1
        simp [inside] at read
      have old : before.values[index]? = some (.unenumerated pendingNode pendingScs) := by simpa [Ne.symm notSelected] using read
      have indexFixed := stored_root_fixed before safe roots paths index _ old (by simp)
      simp [nextLevel, indexFixed, notSelected, stratified.pending index pendingNode pendingScs old]
  exact ⟨nextLevel, nextOrder, increases, oldExpanded⟩

end MicroCFTA.EnumerationOrder

#check MicroCFTA.EnumerationOrder.stratified_preserved_with_old_levels
#print axioms MicroCFTA.EnumerationOrder.stratified_preserved_with_old_levels
#check MicroCFTA.EnumerationOrder.write_stratified_with_old_levels
#print axioms MicroCFTA.EnumerationOrder.write_stratified_with_old_levels
