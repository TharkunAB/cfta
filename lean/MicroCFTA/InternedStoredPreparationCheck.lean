import MicroCFTA.InternedStoredClosedMuCompletion

/-!
# Finite check for the stored-body preparation predicate

Prepared traversal stops at an opaque closed record. An open Mu requires
a dynamic binder request. Ordinary records check their actual children.
The Boolean check has exactly the existing preparation predicate.
-/
namespace MicroCFTA.InternedStoredPreparationCheck
open InternedConstructorTemplates InternedStoredClosedMuCompletion

mutual
/-- Check preparation through actual open children and stop at closed records. -/
def check (value : Value Symbol Guard) : Bool :=
  if value.free.isEmpty then true else
    match value with
    | .mu .. => false
    | .node _ edges _ _ => checkEdges edges
    | .union _ members _ _ => checkMany members
    | _ => true
termination_by sizeOf value

/-- Check each actual ordered member. -/
def checkMany : List (Value Symbol Guard) → Bool
  | [] => true
  | first :: rest => check first && checkMany rest
termination_by values => sizeOf values

/-- Check each actual ordered edge child. -/
def checkEdges : List (EdgeValue Symbol Guard) → Bool
  | [] => true
  | .mk _ children :: rest => checkMany children && checkEdges rest
termination_by edges => sizeOf edges
end

/-- The member check accepts exactly when every member passes. -/
theorem checkMany_eq_true (values : List (Value Symbol Guard)) :
    checkMany values = true ↔ ∀ value ∈ values, check value = true := by
  induction values with
  | nil => simp [checkMany]
  | cons first rest ih => simp [checkMany, ih]

/-- The edge check accepts exactly when every actual child passes. -/
theorem checkEdges_eq_true (edges : List (EdgeValue Symbol Guard)) :
    checkEdges edges = true ↔ ∀ value ∈ edges.flatMap EdgeValue.children, check value = true := by
  induction edges with
  | nil => simp [checkEdges]
  | cons first rest ih =>
      cases first
      rename_i entry children
      simp only [checkEdges, Bool.and_eq_true, checkMany_eq_true, ih, List.flatMap_cons, EdgeValue.children]
      constructor
      · intro both value member
        rcases List.mem_append.mp member with own | later
        · exact both.1 value own
        · exact both.2 value later
      · intro all
        exact ⟨fun value member => all value (List.mem_append_left _ member),
          fun value member => all value (List.mem_append_right _ member)⟩

/-- Every body with the existing preparation proof passes the finite check. -/
theorem of_prepared (value : Value Symbol Guard) (prepared : PreparedWithoutMu value) : check value = true := by
  induction prepared with
  | closed value free => simp only [check.eq_def, free, List.isEmpty_nil, ite_true]
  | empty | reference => simp [check.eq_def, Value.free]
  | node entry edges depth free children ih =>
      rw [check.eq_def]
      split
      · rfl
      · exact checkEdges_eq_true edges |>.mpr ih
  | union entry members depth free children ih =>
      rw [check.eq_def]
      split
      · rfl
      · exact checkMany_eq_true members |>.mpr ih

/-- Every accepted finite check derives the original preparation predicate. -/
theorem prepared_of_check (value : Value Symbol Guard) (checked : check value = true) : PreparedWithoutMu value := by
  rw [check.eq_def] at checked
  split at checked
  · exact .closed value (by simpa only [List.isEmpty_iff] using ‹value.free.isEmpty = true›)
  · cases value with
    | empty => exact .empty
    | reference name => exact .reference name
    | mu => cases checked
    | node entry edges depth free =>
        apply PreparedWithoutMu.node
        intro child member
        exact prepared_of_check child ((checkEdges_eq_true edges).mp checked child member)
    | union entry members depth free =>
        apply PreparedWithoutMu.union
        intro child member
        exact prepared_of_check child ((checkMany_eq_true members).mp checked child member)
termination_by sizeOf value
decreasing_by
  · obtain ⟨edge, included, inner⟩ := List.mem_flatMap.mp member
    have outerSize := List.sizeOf_lt_of_mem included
    have innerSize := List.sizeOf_lt_of_mem inner
    cases edge
    simp_all only [EdgeValue.children]
    simp_wf
    simp_all only [EdgeValue.mk.sizeOf_spec]
    omega
  · have smaller := List.sizeOf_lt_of_mem member
    simp_wf
    simp_all only [Value.union.sizeOf_spec]
    omega

/-- The finite check is equivalent to the existing stored-body preparation predicate. -/
theorem check_eq_true (value : Value Symbol Guard) : check value = true ↔ PreparedWithoutMu value :=
  ⟨prepared_of_check value, of_prepared value⟩

/-- A rejected finite check refutes preparation for the actual stored body. -/
theorem not_prepared (value : Value Symbol Guard) (rejected : check value = false) : ¬ PreparedWithoutMu value := by
  intro prepared
  have accepted := of_prepared value prepared
  rw [rejected] at accepted
  cases accepted

end MicroCFTA.InternedStoredPreparationCheck
