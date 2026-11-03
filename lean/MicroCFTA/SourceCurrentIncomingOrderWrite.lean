import MicroCFTA.SourceCurrentIncomingPendingWrite
import MicroCFTA.EnumerationOrder

/-! An unenumerated replacement preserves the original levels at a fixed forest. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingOrderWrite
open EnumerationState

private theorem set_lookup_source {α : Type} (values : List α) (target held : Nat)
    (replacement value : α) :
    (values.set target replacement)[held]? = some value → held = target ∨ values[held]? = some value := by
  induction values generalizing target held with
  | nil => simp
  | cons head tail inductionHyp =>
      intro observed
      cases target with
      | zero =>
          cases held with
          | zero => exact Or.inl rfl
          | succ held => exact Or.inr (by simpa using observed)
      | succ target =>
          cases held with
          | zero => exact Or.inr (by simpa using observed)
          | succ held =>
              rcases inductionHyp target held (by simpa using observed) with same | original
              · exact Or.inl (congrArg Nat.succ same)
              · exact Or.inr (by simpa using original)

/-- The original stored slot supplies its level for either replacement handle option. -/
theorem stratified_unenumerated_set {Symbol Guard : Type} (before : State Symbol Guard)
    (target : Nat) (oldNode node : Option Nat) (oldScs scs : List Suspended)
    (level : Nat → Nat) (frontier : Nat)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (ordered : EnumerationOrder.Stratified before level frontier) :
    EnumerationOrder.Stratified
      {before with values := before.values.set target (.unenumerated node scs)} level frontier := by
  refine ⟨ordered.classes, ?_, ?_⟩
  · intro held fragment observed
    exact ordered.expanded held fragment
      (SourceCurrentIncomingPendingWrite.unenumerated_set_origin before.values node scs target held fragment observed)
  · intro held foundNode foundScs observed
    rcases set_lookup_source before.values target held (.unenumerated node scs)
      (.unenumerated foundNode foundScs) observed with same | original
    · subst held
      exact ordered.pending target oldNode oldScs stored
    · exact ordered.pending held foundNode foundScs original

end MicroCFTA.SourceCurrentIncomingOrderWrite
