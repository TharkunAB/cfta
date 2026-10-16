import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain

/-!
# Literal ordinary constructor occurrence counts

Counts retain repeated positions in rows and child forests.
One ordinary node contributes one node occurrence.
One edge contributes one edge occurrence and all of its children.
Recursive heads are outside the finite ordinary accounting domain.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOccurrences
open Cache InternedConstructorTemplates
variable {Symbol Guard : Type}

mutual
/-- Count every literal ordinary node and edge below an original node. -/
def node : Value Symbol Guard → Nat × Nat
  | .node _ edges _ _ => (1 + (rows edges).1, (rows edges).2)
  | _ => (0, 0)

/-- Add every source row occurrence, including repeated rows. -/
def rows : List (EdgeValue Symbol Guard) → Nat × Nat
  | [] => (0, 0)
  | first :: rest => ((edge first).1 + (rows rest).1, (edge first).2 + (rows rest).2)

/-- Include the source edge and all literal child occurrences. -/
def edge : EdgeValue Symbol Guard → Nat × Nat
  | .mk _ values => ((children values).1, 1 + (children values).2)

/-- Add every source child occurrence, including repeated values. -/
def children : List (Value Symbol Guard) → Nat × Nat
  | [] => (0, 0)
  | first :: rest => ((node first).1 + (children rest).1, (node first).2 + (children rest).2)
end

/-- Any selected child consumes no more than its complete source forest. -/
theorem child_member (values : List (Value Symbol Guard)) (value : Value Symbol Guard)
    (member : value ∈ values) : (node value).1 ≤ (children values).1 ∧ (node value).2 ≤ (children values).2 := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
      · have smaller := ih later
        exact ⟨by simpa only [children] using Nat.le_trans smaller.1 (Nat.le_add_left _ _),
          by simpa only [children] using Nat.le_trans smaller.2 (Nat.le_add_left _ _)⟩

/-- Any selected edge consumes no more than its complete original row list. -/
theorem edge_member (values : List (EdgeValue Symbol Guard)) (value : EdgeValue Symbol Guard)
    (member : value ∈ values) : (edge value).1 ≤ (rows values).1 ∧ (edge value).2 ≤ (rows values).2 := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
      · have smaller := ih later
        exact ⟨by simpa only [rows] using Nat.le_trans smaller.1 (Nat.le_add_left _ _),
          by simpa only [rows] using Nat.le_trans smaller.2 (Nat.le_add_left _ _)⟩

/-- A selected child fits the node occurrences below its own original row. -/
theorem edge_child (value : EdgeValue Symbol Guard) (child : Value Symbol Guard) (member : child ∈ value.children) :
    (node child).1 ≤ (edge value).1 := by
  cases value with
  | mk entry values => exact (child_member values child member).1

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOccurrences
