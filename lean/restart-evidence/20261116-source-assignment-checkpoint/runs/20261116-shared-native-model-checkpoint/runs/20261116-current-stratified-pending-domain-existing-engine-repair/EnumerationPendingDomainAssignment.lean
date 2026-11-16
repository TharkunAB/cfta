import MicroCFTA.EnumerationPendingAssignment

/-!
# One current assignment with a common pending-domain member

The existing finite evaluator extends the constant pending choice.
The resulting assignment satisfies UF aliases, stored fragment equations
and each present pending domain. Pending buckets have no obligations.
This result does not cover historical buckets, residual guards or root acceptance.
-/
namespace MicroCFTA.EnumerationPendingAssignment
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationOrder

set_option autoImplicit false
variable {Symbol Guard : Type}

/-- Extend one common pending-domain member to all current slots and UF aliases. -/
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
  obtain ⟨assignment, aliases, equations, pendingValue⟩ :=
    stratified_extend_pending state safe level frontier stratified
      (fun _ => fallback) (fun _ _ _ => rfl)
  refine ⟨assignment, ⟨aliases, ?_⟩, pendingValue⟩
  intro uv
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
          exact (equations uv fragment stored).symm

end MicroCFTA.EnumerationPendingAssignment
