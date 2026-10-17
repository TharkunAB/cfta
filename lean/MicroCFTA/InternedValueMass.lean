import MicroCFTA.InternedConstructorTemplates

/-!
# Structural mass of complete constructor payloads

Mass counts value, edge, and list constructors. It ignores keys, identities,
free-name fields, cached depth, symbols, and guards. Mu includes its body and
both stored probes. The caller's SizeOf instances give a separate upper bound.
Mass is not a byte count or an instruction cost.
-/
namespace MicroCFTA.InternedValueMass
open InternedConstructorTemplates
variable {Symbol Guard : Type}

mutual
/-- Count the structural payload of a value, including all three Mu fields. -/
def value : Value Symbol Guard → Nat
  | .empty | .reference _ => 1
  | .node _ rows _ _ => 1 + edges rows
  | .union _ members _ _ => 1 + values members
  | .mu _ body depth ordinary => 1 + value body + value depth + value ordinary
termination_by node => sizeOf node

/-- Count an edge constructor and its complete ordered child payloads. -/
def edge : EdgeValue Symbol Guard → Nat
  | .mk _ children => 1 + values children
termination_by row => sizeOf row

/-- Count one list constructor and the complete payload at every position. -/
def values : List (Value Symbol Guard) → Nat
  | [] => 0
  | first :: rest => 1 + value first + values rest
termination_by nodes => sizeOf nodes

/-- Count one list constructor and the complete row payload at every position. -/
def edges : List (EdgeValue Symbol Guard) → Nat
  | [] => 0
  | first :: rest => 1 + edge first + edges rest
termination_by rows => sizeOf rows
end

/-- Every value has positive structural mass. -/
theorem value_pos (node : Value Symbol Guard) : 0 < value node := by
  cases node <;> simp only [value] <;> omega

/-- Every complete edge has positive structural mass. -/
theorem edge_pos (row : EdgeValue Symbol Guard) : 0 < edge row := by
  cases row
  simp only [edge]
  omega

/-- The complete child-list mass determines the edge mass. -/
theorem edge_children (row : EdgeValue Symbol Guard) : edge row = 1 + values row.children := by
  cases row
  simp only [edge, EdgeValue.children]

/-- Appending immutable value lists adds their structural masses. -/
theorem values_append (first last : List (Value Symbol Guard)) : values (first ++ last) = values first + values last := by
  induction first with
  | nil => simp only [List.nil_append, values, Nat.zero_add]
  | cons first rest ih => simp only [List.cons_append, values, ih]; omega

/-- Appending immutable row lists adds their structural masses. -/
theorem edges_append (first last : List (EdgeValue Symbol Guard)) : edges (first ++ last) = edges first + edges last := by
  induction first with
  | nil => simp only [List.nil_append, edges, Nat.zero_add]
  | cons first rest ih => simp only [List.cons_append, edges, ih]; omega

/-- Value-list mass is its length plus the sum of the complete value masses. -/
theorem values_eq_length_sum (nodes : List (Value Symbol Guard)) :
    values nodes = nodes.length + (nodes.map value).sum := by
  induction nodes with
  | nil => simp only [values, List.length_nil, List.map_nil, List.sum_nil, Nat.zero_add]
  | cons first rest ih => simp only [values, List.length_cons, List.map_cons, List.sum_cons, ih]; omega

/-- Row-list mass is its length plus the sum of the complete edge masses. -/
theorem edges_eq_length_sum (rows : List (EdgeValue Symbol Guard)) :
    edges rows = rows.length + (rows.map edge).sum := by
  induction rows with
  | nil => simp only [edges, List.length_nil, List.map_nil, List.sum_nil, Nat.zero_add]
  | cons first rest ih => simp only [edges, List.length_cons, List.map_cons, List.sum_cons, ih]; omega

/-- Removing value occurrences cannot increase structural mass. -/
theorem values_filter (predicate : Value Symbol Guard → Bool) (nodes : List (Value Symbol Guard)) :
    values (nodes.filter predicate) ≤ values nodes := by
  induction nodes with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
      cases selected : predicate first <;> simp [selected, values] <;> omega

/-- Removing row occurrences cannot increase structural mass. -/
theorem edges_filter (predicate : EdgeValue Symbol Guard → Bool) (rows : List (EdgeValue Symbol Guard)) :
    edges (rows.filter predicate) ≤ edges rows := by
  induction rows with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
      cases selected : predicate first <;> simp [selected, edges] <;> omega

/-- Each retained value occurrence has smaller mass than its containing list. -/
theorem value_mem_lt (node : Value Symbol Guard) (nodes : List (Value Symbol Guard)) (member : node ∈ nodes) :
    value node < values nodes := by
  induction nodes with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst node; simp only [values]; omega
      · have small := ih later; simp only [values]; omega

/-- Each retained row occurrence has smaller mass than its containing list. -/
theorem edge_mem_lt (row : EdgeValue Symbol Guard) (rows : List (EdgeValue Symbol Guard)) (member : row ∈ rows) :
    edge row < edges rows := by
  induction rows with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst row; simp only [edges]; omega
      · have small := ih later; simp only [edges]; omega

/-- An ordinary child's complete payload has smaller mass than its parent. -/
theorem node_child_lt (entry) (rows : List (EdgeValue Symbol Guard)) (level free)
    (row : EdgeValue Symbol Guard) (member : row ∈ rows) (child : Value Symbol Guard) (inside : child ∈ row.children) :
    value child < value (.node entry rows level free) := by
  have first := value_mem_lt child row.children inside
  have last := edge_mem_lt row rows member
  rw [edge_children] at last
  simp only [value]
  omega

/-- Every stored union alternative has smaller mass than its union. -/
theorem union_member_lt (entry) (members : List (Value Symbol Guard)) (level free)
    (child : Value Symbol Guard) (member : child ∈ members) : value child < value (.union entry members level free) := by
  have small := value_mem_lt child members member
  simp only [value]
  omega

/-- The stored Mu body has smaller mass than its complete Mu. -/
theorem mu_body_lt (entry) (body depth ordinary : Value Symbol Guard) : value body < value (.mu entry body depth ordinary) := by
  simp only [value]
  omega

/-- The stored depth probe has smaller mass than its complete Mu. -/
theorem mu_depth_lt (entry) (body depth ordinary : Value Symbol Guard) : value depth < value (.mu entry body depth ordinary) := by
  simp only [value]
  omega

/-- The stored ordinary probe has smaller mass than its complete Mu. -/
theorem mu_ordinary_lt (entry) (body depth ordinary : Value Symbol Guard) : value ordinary < value (.mu entry body depth ordinary) := by
  simp only [value]
  omega

section CallerSize
variable [SizeOf Symbol] [SizeOf Guard]

mutual
/-- The caller's complete value SizeOf bounds the metadata-free structural mass. -/
theorem value_le_sizeOf (node : Value Symbol Guard) : value node ≤ sizeOf node := by
  cases node with
  | empty => simp only [value, Value.empty.sizeOf_spec]; omega
  | reference name => simp only [value, Value.reference.sizeOf_spec]; omega
  | node entry rows level free =>
      have smaller := edges_le_sizeOf rows
      simp only [value, Value.node.sizeOf_spec]
      omega
  | union entry members level free =>
      have smaller := values_le_sizeOf members
      simp only [value, Value.union.sizeOf_spec]
      omega
  | mu entry body depth ordinary =>
      have bodyBound := value_le_sizeOf body
      have depthBound := value_le_sizeOf depth
      have ordinaryBound := value_le_sizeOf ordinary
      simp only [value, Value.mu.sizeOf_spec]
      omega
termination_by sizeOf node

/-- The caller's complete edge SizeOf bounds its structural mass. -/
theorem edge_le_sizeOf (row : EdgeValue Symbol Guard) : edge row ≤ sizeOf row := by
  cases row with
  | mk entry children =>
      have smaller := values_le_sizeOf children
      simp only [edge, EdgeValue.mk.sizeOf_spec]
      omega
termination_by sizeOf row

/-- The caller's complete value-list SizeOf bounds the structural list mass. -/
theorem values_le_sizeOf (nodes : List (Value Symbol Guard)) : values nodes ≤ sizeOf nodes := by
  cases nodes with
  | nil => simp only [values]; omega
  | cons first rest =>
      have firstBound := value_le_sizeOf first
      have restBound := values_le_sizeOf rest
      simp only [values, List.cons.sizeOf_spec]
      omega
termination_by sizeOf nodes

/-- The caller's complete row-list SizeOf bounds the structural list mass. -/
theorem edges_le_sizeOf (rows : List (EdgeValue Symbol Guard)) : edges rows ≤ sizeOf rows := by
  cases rows with
  | nil => simp only [edges]; omega
  | cons first rest =>
      have firstBound := edge_le_sizeOf first
      have restBound := edges_le_sizeOf rest
      simp only [edges, List.cons.sizeOf_spec]
      omega
termination_by sizeOf rows
end
end CallerSize
end MicroCFTA.InternedValueMass
