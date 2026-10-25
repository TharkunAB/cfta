import MicroCFTA.EnumerationOrder

/-!
# Transport of stored fragment dependency levels

Preserved expanded slots keep their old levels. Other representative classes
receive the current frontier level.
-/
namespace MicroCFTA.EnumerationOrder
open Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationDriver EnumerationDependencies

/-- Origin and protected expanded classes retain a strict fragment dependency order. -/
theorem stratified_preserved (before after : State Symbol Guard)
    (afterSafe : Safe after) (level : Nat → Nat) (frontier : Nat)
    (stratified : Stratified before level frontier) (origin : EnumeratedOrigin before after)
    (protects : ∀ held fragment, before.values[held]? = some (.enumerated fragment) →
      Protected held before after) :
    ∃ nextLevel, Stratified after nextLevel frontier := by
  obtain ⟨roots, paths⟩ := roots_exist after.representatives afterSafe.1.total
  let nextLevel := fun uv => match after.values[roots uv]? with
    | some (.enumerated _) => level (roots uv)
    | _ => frontier
  have fixedExpanded : ∀ uv storedFragment,
      after.values[uv]? = some (.enumerated storedFragment) → nextLevel uv = level uv := by
    intro uv storedFragment stored
    have fixed := stored_root_fixed after afterSafe roots paths uv _ stored (by simp)
    simp [nextLevel, fixed, stored]
  refine ⟨nextLevel, ?_, ?_, ?_⟩
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

end MicroCFTA.EnumerationOrder
