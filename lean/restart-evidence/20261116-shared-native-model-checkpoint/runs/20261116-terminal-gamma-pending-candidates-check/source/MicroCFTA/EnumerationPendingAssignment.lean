import MicroCFTA.EnumerationAssignment

/-!
# One assignment for current pending domains and stored equations

Pending slots have no suspended obligations. One fixed finite fallback term
belongs to each pending slot's present domain. The existing stratified evaluator
then satisfies the forest, every stored fragment equation and each pending domain.
This statement does not include removed obligations or retained residual guards.
It does not prove acceptance of the original source root.
-/
namespace MicroCFTA.EnumerationPendingAssignment
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver
open EnumerationSemantics EnumerationFrame EnumerationValidity EnumerationSoundness EnumerationProgress
open EnumerationDependencies EnumerationReferences EnumerationOrder EnumerationAssignment

set_option autoImplicit false
variable {Symbol Guard : Type}

/-- One finite evaluator satisfies current equations and compatible empty pending slots. -/
theorem stratified_pending_assignment
    (state : State Symbol Guard) (safe : Safe state) (level : Nat → Nat) (frontier : Nat)
    (stratified : Stratified state level frontier) (fallback : Term Symbol) (language : NodeLanguage Symbol)
    (pending : ∀ (uv : Nat) (node : Option Nat) (scs : List Suspended),
      state.values[uv]? = some (.unenumerated node scs) →
      scs = [] ∧ ∀ handle, node = some handle → language handle fallback) :
    ∃ assignment : Nat → Term Symbol,
      Fragments.stateSatisfies state.representatives (heap language state.values) assignment ∧
      ∀ (uv : Nat) (node : Option Nat) (scs : List Suspended),
        state.values[uv]? = some (.unenumerated node scs) → assignment uv = fallback
 := by
  obtain ⟨roots, paths⟩ := roots_exist state.representatives safe.1.total
  let assignment := evaluateSlots state.values roots fallback (frontier + 1)
  have pendingValue : ∀ (uv : Nat) (node : Option Nat) (scs : List Suspended),
      state.values[uv]? = some (.unenumerated node scs) → assignment uv = fallback := by
    intro uv node scs stored
    have fixed := stored_root_fixed state safe roots paths uv _ stored (by simp)
    simp only [assignment, evaluateSlots, fixed, stored]
  refine ⟨assignment, ⟨?_, ?_⟩, pendingValue⟩
  · intro left right same
    have sameRoot := (class_iff state.representatives roots paths left right).mp same
    simp [assignment, evaluateSlots, sameRoot]
  · intro uv
    cases stored : state.values[uv]? with
    | none => simp [heap, stored, slot, slotSatisfies]
    | some value =>
        cases value with
        | eliminated => simp [heap, stored, slot, slotSatisfies]
        | unenumerated node scs =>
            obtain ⟨rfl, domains⟩ := pending uv node scs stored
            have assigned := pendingValue uv node [] stored
            cases node with
            | none => simp [heap, stored, slot, slotSatisfies, permits]
            | some handle =>
                have member := domains handle rfl
                simpa [heap, stored, slot, slotSatisfies, permits, assigned] using member
        | enumerated fragment =>
            simp only [heap, stored, Option.getD_some, slot, slotSatisfies]
            have fixed := stored_root_fixed state safe roots paths uv _ stored (by simp)
            change fill assignment fragment = evaluateSlots state.values roots fallback (frontier + 1) uv
            rw [evaluateSlots, fixed, stored]
            apply fill_holes_congr
            intro hole present
            obtain ⟨bound, dependencies⟩ := stratified.expanded uv fragment stored
            have higher := dependencies hole present
            exact evaluateSlots_stable state roots paths level frontier stratified fallback
              hole (frontier + 1) frontier (by omega) (by omega)

end MicroCFTA.EnumerationPendingAssignment

#print axioms MicroCFTA.EnumerationPendingAssignment.stratified_pending_assignment
