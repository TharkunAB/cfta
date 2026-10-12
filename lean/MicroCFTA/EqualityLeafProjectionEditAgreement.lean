import MicroCFTA.EqualityLeafProjectionEditExact

/-!
# Stateful congruence of simultaneous edit closures

Local intersection agreement in grown valid caches determines the complete
edit trace. The proof preserves state effects and selected target order.
-/
namespace MicroCFTA.EqualityLeafProjectionEditAgreement
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionWorkers
open EqualityLeafProjectionSyntax (Path atRoot descendEdits descendEdits_member)

/-- Two requests return the same result and cache in every retained valid cache. -/
def Agree [DecidableEq (EdgeKey Symbol Guard)] (base : State Symbol Guard)
    (first second : Work Symbol Guard Result) : Prop :=
  ∀ state, Valid state → Grows base state → run first state = run second state

/-- Equal requests agree in each later cache. -/
theorem agree_refl [DecidableEq (EdgeKey Symbol Guard)] (base : State Symbol Guard) (work : Work Symbol Guard Result) :
    Agree base work work := fun _ _ _ => rfl

/-- Ordered source effects compose agreement without changing intermediate states. -/
theorem agree_bind [DecidableEq (EdgeKey Symbol Guard)] (base : State Symbol Guard)
    (first second : Work Symbol Guard Input) (next next' : Input → Work Symbol Guard Result)
    (initial : Agree base first second) (suffix : ∀ value, Agree base (next value) (next' value)) :
    Agree base (first.bind next) (second.bind next') := by
  intro state valid growth
  simp only [run_bind]
  have correct := InternedConstructorTemplates.run_correct first state valid
  have same := initial state valid growth
  rw [← same]
  exact suffix (run first state).1 (run first state).2 correct.1 (grows_trans growth correct.2)

/-- Optional worker failure and success preserve the same source effects. -/
theorem agree_optional [DecidableEq (EdgeKey Symbol Guard)] (base : State Symbol Guard)
    (first second : Work Symbol Guard (Option Input)) (next next' : Input → Work Symbol Guard (Option Result))
    (initial : Agree base first second) (suffix : ∀ value, Agree base (next value) (next' value)) :
    Agree base (bindOptional first next) (bindOptional second next') := by
  apply agree_bind base first second _ _ initial
  intro value
  cases value with
  | none => exact agree_refl base _
  | some value => exact suffix value

/-- The first selected root target is an actual empty-path entry. -/
theorem atRoot_member (edits : List (Path × Target)) (target : Target) (found : atRoot edits = some target) :
    ([], target) ∈ edits := by
  unfold atRoot at found
  obtain ⟨pair, selected, same⟩ := Option.map_eq_some_iff.mp found
  have present := List.mem_of_find?_eq_some selected
  have root := List.find?_some selected
  have pathEmpty : pair.1 = [] := List.isEmpty_iff.mp root
  cases pair with
  | mk path value =>
      dsimp only at same pathEmpty
      subst path
      subst value
      exact present

mutual
/-- Local target intersection agreement derives the full source edit run. -/
theorem edit_agree [DecidableEq (EdgeKey Symbol Guard)] (base : State Symbol Guard)
    (first second : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (edits : List (Path × Target))
    (localAgreement : ∀ path target, (path, target) ∈ edits → ∀ value, Agree base (first target value) (second target value))
    (value : Value Symbol Guard) : Agree base (edit first edits value) (edit second edits value) := by
  cases edits with
  | nil =>
      rw [edit_unselected, edit_unselected]
      exact agree_refl base _
  | cons selected rest =>
      cases value with
      | empty => exact agree_refl base _
      | reference | union | mu => exact agree_refl base _
      | node entry edges depth free =>
          rw [edit, edit]
          cases root : atRoot (selected :: rest) with
          | some target =>
              exact agree_bind base _ _ _ _ (localAgreement [] target (atRoot_member _ _ root) _) (fun _ => agree_refl base _)
          | none =>
              exact agree_optional base _ _ _ _ (edges_agree base first second (selected :: rest) localAgreement edges)
                (fun _ => agree_refl base _)
termination_by sizeOf value

/-- Original edge order and complete constructor requests preserve local agreement. -/
theorem edges_agree [DecidableEq (EdgeKey Symbol Guard)] (base : State Symbol Guard)
    (first second : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (edits : List (Path × Target))
    (localAgreement : ∀ path target, (path, target) ∈ edits → ∀ value, Agree base (first target value) (second target value))
    (edges : List (EdgeValue Symbol Guard)) : Agree base (editEdges first edits edges) (editEdges second edits edges) := by
  cases edges with
  | nil => exact agree_refl base _
  | cons edge rest =>
      cases edge with
      | mk entry children =>
          rw [editEdges, editEdges]
          apply agree_optional base _ _ _ _ (children_agree base first second edits localAgreement 0 children)
          intro nodes
          apply agree_bind base _ _ _ _ (agree_refl base _)
          intro edge
          exact agree_optional base _ _ _ _ (edges_agree base first second edits localAgreement rest) (fun _ => agree_refl base _)
termination_by sizeOf edges

/-- Selected path suffixes retain the same target closure at each original child position. -/
theorem children_agree [DecidableEq (EdgeKey Symbol Guard)] (base : State Symbol Guard)
    (first second : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (edits : List (Path × Target))
    (localAgreement : ∀ path target, (path, target) ∈ edits → ∀ value, Agree base (first target value) (second target value))
    (index : Nat) (children : List (Value Symbol Guard)) :
    Agree base (editChildren first edits index children) (editChildren second edits index children) := by
  cases children with
  | nil => exact agree_refl base _
  | cons child rest =>
      rw [editChildren, editChildren]
      apply agree_optional base _ _ _ _ (edit_agree base first second (descendEdits edits index)
        (fun path target member => localAgreement (index :: path) target (descendEdits_member edits index path target member)) child)
      intro node
      exact agree_optional base _ _ _ _ (children_agree base first second edits localAgreement (index + 1) rest)
        (fun _ => agree_refl base _)
termination_by sizeOf children
end

end MicroCFTA.EqualityLeafProjectionEditAgreement
