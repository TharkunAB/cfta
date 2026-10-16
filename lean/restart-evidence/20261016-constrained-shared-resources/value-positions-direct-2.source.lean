import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds

/-!
# Literal finite ordinary value positions

Empty contributes one position. Ordinary rows retain every literal child
position, including repeated values and rows. Recursive and union heads are
opaque positions. The profile bounds apply only to finite ordinary values.
These counts do not assume execution or callback behavior.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryValuePositions
open InternedConstructorTemplates
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open MergedOrdinaryHeight (height childrenHeight)
local notation "OrdinaryNode" => SourceCurrentAllocatedFiniteOrdinaryOccurrences.node
local notation "OrdinaryRows" => SourceCurrentAllocatedFiniteOrdinaryOccurrences.rows
local notation "OrdinaryEdge" => SourceCurrentAllocatedFiniteOrdinaryOccurrences.edge
local notation "OrdinaryChildren" => SourceCurrentAllocatedFiniteOrdinaryOccurrences.children
local notation "EdgeCount" => SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.edgeCount
variable {Symbol Guard : Type} {rowLimit arityLimit : Nat}

mutual
/-- Count the root and all literal ordinary child positions. -/
def node : Value Symbol Guard → Nat
  | .node _ edges _ _ => 1 + rows edges
  | _ => 1

/-- Add every row's value positions in source order. -/
def rows : List (EdgeValue Symbol Guard) → Nat
  | [] => 0
  | first :: rest => edge first + rows rest

/-- An edge contributes the positions of its complete child forest. -/
def edge : EdgeValue Symbol Guard → Nat
  | .mk _ values => children values

/-- Add every literal child position, including Empty and repeated values. -/
def children : List (Value Symbol Guard) → Nat
  | [] => 0
  | first :: rest => node first + children rest
end

/-- Empty is one value position. -/
theorem node_empty : node (.empty : Value Symbol Guard) = 1 := rfl

/-- Every value contributes its root position. -/
theorem node_pos (value : Value Symbol Guard) : 0 < node value := by
  cases value <;> simp only [node] <;> omega

/-- Ordered row concatenation adds both occurrence counts. -/
theorem rows_append (first last : List (EdgeValue Symbol Guard)) :
    rows (first ++ last) = rows first + rows last := by
  induction first with
  | nil => simp [rows]
  | cons head rest ih => simp [rows, ih, Nat.add_assoc]

/-- Ordered forest concatenation retains all positions from both lists. -/
theorem children_append (first last : List (Value Symbol Guard)) :
    children (first ++ last) = children first + children last := by
  induction first with
  | nil => simp [children]
  | cons head rest ih => simp [children, ih, Nat.add_assoc]

/-- Every forest contains at least one position for each root. -/
theorem length_le_children (values : List (Value Symbol Guard)) : values.length ≤ children values := by
  induction values with
  | nil => simp [children]
  | cons first rest ih =>
      have positive := node_pos first
      simp only [children, List.length_cons]
      omega

/-- A selected child uses no more positions than its complete ordered forest. -/
theorem child_member (values : List (Value Symbol Guard)) (value : Value Symbol Guard)
    (member : value ∈ values) : node value ≤ children values := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_add_right _ _
      · exact Nat.le_trans (ih later) (Nat.le_add_left _ _)

/-- A selected row uses no more positions than its complete ordered row list. -/
theorem edge_member (values : List (EdgeValue Symbol Guard)) (value : EdgeValue Symbol Guard)
    (member : value ∈ values) : edge value ≤ rows values := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_add_right _ _
      · exact Nat.le_trans (ih later) (Nat.le_add_left _ _)

mutual
/-- Each non-root position belongs to one literal row's child list. -/
theorem node_edges (value : Value Symbol Guard) (profile : NodeShape rowLimit arityLimit value) :
    node value ≤ 1 + arityLimit * (OrdinaryNode value).2 := by
  cases value with
  | empty => simp [node, OrdinaryNode]
  | reference | mu | union => cases profile
  | node entry edges depth free =>
      exact Nat.add_le_add_left (rows_edges edges profile.2) 1
termination_by sizeOf value

/-- Uniform arity bounds all child positions below the literal rows. -/
theorem rows_edges (values : List (EdgeValue Symbol Guard)) (profile : RowsShape rowLimit arityLimit values) :
    rows values ≤ arityLimit * (OrdinaryRows values).2 := by
  cases values with
  | nil => simp [rows, OrdinaryRows]
  | cons first rest =>
      have firstBound := edge_edges first profile.1
      have restBound := rows_edges rest profile.2
      simpa only [rows, OrdinaryRows, Nat.mul_add] using Nat.add_le_add firstBound restBound
termination_by sizeOf values

/-- An edge charges its own child positions and all descendant row positions. -/
theorem edge_edges (value : EdgeValue Symbol Guard) (profile : EdgeShape rowLimit arityLimit value) :
    edge value ≤ arityLimit * (OrdinaryEdge value).2 := by
  cases value with
  | mk entry values =>
      calc
        children values ≤ values.length + arityLimit * (OrdinaryChildren values).2 := children_edges values profile.2
        _ ≤ arityLimit + arityLimit * (OrdinaryChildren values).2 := Nat.add_le_add_right profile.1 _
        _ = arityLimit * (OrdinaryEdge (.mk entry values)).2 := by simp [OrdinaryEdge, Nat.mul_add]
termination_by sizeOf value

/-- Forest roots and literal row arities bound every value position. -/
theorem children_edges (values : List (Value Symbol Guard)) (profile : ChildrenShape rowLimit arityLimit values) :
    children values ≤ values.length + arityLimit * (OrdinaryChildren values).2 := by
  cases values with
  | nil => simp [children, OrdinaryChildren]
  | cons first rest =>
      have firstBound := node_edges first profile.1
      have restBound := children_edges rest profile.2
      simp only [children, OrdinaryChildren, List.length_cons, Nat.mul_add]
      omega
termination_by sizeOf values
end

/-- Initial row, arity, and height limits bound all positions of one value. -/
theorem profile_node (value : Value Symbol Guard) (profile : NodeShape rowLimit arityLimit value)
    (bound : Nat) (heightBound : height value ≤ bound) :
    node value ≤ 1 + arityLimit * EdgeCount rowLimit arityLimit bound :=
  Nat.le_trans (node_edges value profile)
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.node value profile bound heightBound).2) 1)

/-- An ordered forest multiplies the per-value position bound by its exact length. -/
theorem profile_children (values : List (Value Symbol Guard)) (profile : ChildrenShape rowLimit arityLimit values)
    (bound : Nat) (heightBound : childrenHeight values ≤ bound) :
    children values ≤ values.length * (1 + arityLimit * EdgeCount rowLimit arityLimit bound) := by
  calc
    children values ≤ values.length + arityLimit * (OrdinaryChildren values).2 := children_edges values profile
    _ ≤ values.length + arityLimit * (values.length * EdgeCount rowLimit arityLimit bound) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.children values profile bound heightBound).2) _
    _ = values.length * (1 + arityLimit * EdgeCount rowLimit arityLimit bound) := by
      simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- A declared forest length gives an input-only position bound. -/
theorem profile_forest (values : List (Value Symbol Guard)) (profile : ChildrenShape rowLimit arityLimit values)
    (count bound : Nat) (lengthBound : values.length ≤ count) (heightBound : childrenHeight values ≤ bound) :
    children values ≤ count * (1 + arityLimit * EdgeCount rowLimit arityLimit bound) :=
  Nat.le_trans (profile_children values profile bound heightBound) (Nat.mul_le_mul_right _ lengthBound)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryValuePositions
