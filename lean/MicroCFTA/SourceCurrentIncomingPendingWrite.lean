import MicroCFTA.EnumerationDependencies

/-! Unenumerated slot writes preserve the pending admission of a remaining input bucket. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingPendingWrite
open EnumerationState EnumerationDependencies
variable {Symbol Guard : Type}

/-- An unenumerated replacement cannot create an enumerated slot. -/
theorem unenumerated_set_origin (values : List (UVarValue Symbol)) (node : Option Nat)
    (scs : List Suspended) (target held : Nat) (fragment : Fragments.Fragment Symbol) :
    (values.set target (.unenumerated node scs))[held]? = some (.enumerated fragment) →
    values[held]? = some (.enumerated fragment) := by
  induction values generalizing target held with
  | nil => simp
  | cons head tail inductionHyp =>
      intro observed
      cases target with
      | zero =>
          cases held with
          | zero => simp at observed
          | succ held => simpa using observed
      | succ target =>
          cases held with
          | zero => simpa using observed
          | succ held => exact inductionHyp target held (by simpa using observed)

/-- A remaining input bucket stays pending across the literal slot replacement at a fixed forest. -/
theorem inputs_pending_set (before : EnumerationState.State Symbol Guard) (target : Nat)
    (node : Option Nat) (added remaining : List Suspended)
    (pending : InputsPending before remaining) :
    InputsPending {before with values := before.values.set target (.unenumerated node added)} remaining := by
  intro held fragment observed
  exact pending held fragment (unenumerated_set_origin before.values node added target held fragment observed)

end MicroCFTA.SourceCurrentIncomingPendingWrite
