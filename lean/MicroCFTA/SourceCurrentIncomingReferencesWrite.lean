import MicroCFTA.SourceCurrentIncomingPendingWrite
import MicroCFTA.EnumerationReferences

/-! Original pending references and input admissions permit an unenumerated replacement. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingReferencesWrite
open EnumerationState EnumerationReferences EnumerationDependencies

private theorem all_set {α : Type} (values : List α) (target : Nat)
    (replacement : α) (property : α → Prop) :
    (∀ value ∈ values, property value) → property replacement →
      ∀ value ∈ values.set target replacement, property value := by
  induction values generalizing target with
  | nil => simp
  | cons head tail inductionHyp =>
      intro original permitted
      cases target with
      | zero =>
          intro value member
          rcases List.mem_cons.mp member with same | retained
          · subst value
            exact permitted
          · exact original value (List.mem_cons_of_mem head retained)
      | succ target =>
          intro value member
          rcases List.mem_cons.mp member with same | changed
          · subst value
            exact original head (by simp)
          · exact inductionHyp target
              (fun other retained => original other (List.mem_cons_of_mem head retained)) permitted value changed

/-- Original reference predicates and admitted inputs survive the literal value replacement. -/
theorem references_allowed_set {Symbol Guard : Type} (allowed : Nat → Prop)
    (before : State Symbol Guard) (target : Nat) (node : Option Nat) (scs : List Suspended)
    (original : ReferencesAllowed allowed before) (added : InputsAllowed allowed scs) :
    ReferencesAllowed allowed
      {before with values := before.values.set target (.unenumerated node scs)} :=
  all_set before.values target (.unenumerated node scs)
    _ original added

/-- An original stored payload inherits the original pending-reference admission. -/
theorem stored_inputs_pending {Symbol Guard : Type} (before : State Symbol Guard)
    (target : Nat) (node : Option Nat) (scs : List Suspended)
    (pending : PendingReferences before)
    (stored : before.values[target]? = some (.unenumerated node scs)) :
    InputsPending before scs := by
  intro held fragment observed
  exact pending held fragment observed (.unenumerated node scs) (List.mem_of_getElem? stored)

/-- Original pending references and original incoming admissions suffice at a fixed forest. -/
theorem pending_references_set {Symbol Guard : Type} (before : State Symbol Guard)
    (target : Nat) (node : Option Nat) (scs : List Suspended)
    (pending : PendingReferences before) (added : InputsPending before scs) :
    PendingReferences
      {before with values := before.values.set target (.unenumerated node scs)} := by
  intro held fragment observed
  have original := SourceCurrentIncomingPendingWrite.unenumerated_set_origin before.values
    node scs target held fragment observed
  apply references_allowed_set (fun other => ¬UnionFind.SameClass before.representatives held other)
    before target node scs (pending held fragment original)
  intro sc member sameClass
  exact added held fragment original sc member sameClass

/-- The original stored payload supplies the retained half of the actual reference append. -/
theorem pending_references_append {Symbol Guard : Type} (before : State Symbol Guard)
    (target : Nat) (oldNode node : Option Nat) (scs oldScs : List Suspended)
    (pending : PendingReferences before) (added : InputsPending before scs)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs)) :
    PendingReferences
      {before with values := before.values.set target (.unenumerated node (scs ++ oldScs))} := by
  have retained := stored_inputs_pending before target oldNode oldScs pending stored
  apply pending_references_set before target node (scs ++ oldScs) pending
  intro held fragment observed sc member sameClass
  rcases List.mem_append.mp member with fresh | old
  · exact added held fragment observed sc fresh sameClass
  · exact retained held fragment observed sc old sameClass

end MicroCFTA.SourceCurrentIncomingReferencesWrite
