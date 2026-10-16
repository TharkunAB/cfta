import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain
import MicroCFTA.SourceRecursiveIntersectionKernel

/-!
# Computed row and arity limits for ordinary native inputs

The limits visit every original row and child occurrence.
They bound row counts and arities at all ordinary descendants.
Guards, identities, and cached metadata have no added restriction.
Mu, reference, and explicit union records remain outside the shape predicate.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open Cache InternedConstructorTemplates
open InternedBinderProtocol (NodeKey Reference)
variable {Symbol Guard : Type}

mutual
/-- Every ordinary descendant has the same row and arity limits. -/
def NodeShape (rows arity : Nat) : Value Symbol Guard → Prop
  | .empty => True
  | .node _ edges _ _ => edges.length ≤ rows ∧ RowsShape rows arity edges
  | _ => False

/-- Each literal row retains its complete child profile. -/
def RowsShape (rows arity : Nat) : List (EdgeValue Symbol Guard) → Prop
  | [] => True
  | edge :: rest => EdgeShape rows arity edge ∧ RowsShape rows arity rest

/-- An edge bounds its own arity and every original child profile. -/
def EdgeShape (rows arity : Nat) : EdgeValue Symbol Guard → Prop
  | .mk _ children => children.length ≤ arity ∧ ChildrenShape rows arity children

/-- Every ordered child retains the same uniform profile. -/
def ChildrenShape (rows arity : Nat) : List (Value Symbol Guard) → Prop
  | [] => True
  | value :: rest => NodeShape rows arity value ∧ ChildrenShape rows arity rest
end

mutual
/-- Compute limits from an original ordinary input record. -/
def limits : Value Symbol Guard → Nat × Nat
  | .node _ edges _ _ => (max edges.length (rowsLimits edges).1, (rowsLimits edges).2)
  | _ => (0, 0)

/-- Take both component maxima over every literal source row. -/
def rowsLimits : List (EdgeValue Symbol Guard) → Nat × Nat
  | [] => (0, 0)
  | edge :: rest => (max (edgeLimits edge).1 (rowsLimits rest).1, max (edgeLimits edge).2 (rowsLimits rest).2)

/-- Include the actual child-list length and all nested original profiles. -/
def edgeLimits : EdgeValue Symbol Guard → Nat × Nat
  | .mk _ children => ((childrenLimits children).1, max children.length (childrenLimits children).2)

/-- Take both component maxima over all original child occurrences. -/
def childrenLimits : List (Value Symbol Guard) → Nat × Nat
  | [] => (0, 0)
  | value :: rest => (max (limits value).1 (childrenLimits rest).1, max (limits value).2 (childrenLimits rest).2)
end

variable {rowLimit arityLimit largerRows largerArity : Nat}

mutual
/-- Increasing either limit preserves the whole original node profile. -/
theorem NodeShape.mono (value : Value Symbol Guard) (shape : NodeShape rowLimit arityLimit value)
    (rowBound : rowLimit ≤ largerRows) (arityBound : arityLimit ≤ largerArity) : NodeShape largerRows largerArity value := by
  cases value with
  | empty => trivial
  | node entry edges depth free => exact ⟨Nat.le_trans shape.1 rowBound, RowsShape.mono edges shape.2 rowBound arityBound⟩
  | reference | mu | union => cases shape
termination_by sizeOf value

/-- Increasing either limit preserves every original row. -/
theorem RowsShape.mono (edges : List (EdgeValue Symbol Guard)) (shape : RowsShape rowLimit arityLimit edges)
    (rowBound : rowLimit ≤ largerRows) (arityBound : arityLimit ≤ largerArity) : RowsShape largerRows largerArity edges := by
  cases edges with
  | nil => trivial
  | cons edge rest => exact ⟨EdgeShape.mono edge shape.1 rowBound arityBound, RowsShape.mono rest shape.2 rowBound arityBound⟩
termination_by sizeOf edges

/-- Increasing either limit preserves arity and complete child profiles. -/
theorem EdgeShape.mono (edge : EdgeValue Symbol Guard) (shape : EdgeShape rowLimit arityLimit edge)
    (rowBound : rowLimit ≤ largerRows) (arityBound : arityLimit ≤ largerArity) : EdgeShape largerRows largerArity edge := by
  cases edge with
  | mk entry children => exact ⟨Nat.le_trans shape.1 arityBound, ChildrenShape.mono children shape.2 rowBound arityBound⟩
termination_by sizeOf edge

/-- Increasing either limit preserves the full ordered child forest. -/
theorem ChildrenShape.mono (values : List (Value Symbol Guard)) (shape : ChildrenShape rowLimit arityLimit values)
    (rowBound : rowLimit ≤ largerRows) (arityBound : arityLimit ≤ largerArity) : ChildrenShape largerRows largerArity values := by
  cases values with
  | nil => trivial
  | cons value rest => exact ⟨NodeShape.mono value shape.1 rowBound arityBound, ChildrenShape.mono rest shape.2 rowBound arityBound⟩
termination_by sizeOf values
end

/-- A selected row retains the complete uniform profile. -/
theorem RowsShape.member (edges : List (EdgeValue Symbol Guard)) (shape : RowsShape rowLimit arityLimit edges)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) : EdgeShape rowLimit arityLimit edge := by
  induction edges with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact shape.1
      · exact ih shape.2 later

/-- A selected child retains the complete uniform profile. -/
theorem ChildrenShape.member (values : List (Value Symbol Guard)) (shape : ChildrenShape rowLimit arityLimit values)
    (value : Value Symbol Guard) (member : value ∈ values) : NodeShape rowLimit arityLimit value := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact shape.1
      · exact ih shape.2 later

/-- Ordinary node rows retain their exact order and guards. -/
theorem NodeShape.rows (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List Reference) (shape : NodeShape rowLimit arityLimit (.node entry edges depth free)) :
    RowsShape rowLimit arityLimit edges := shape.2

/-- Empty and ordinary node inputs expose only profiled source rows. -/
theorem NodeShape.nodeEdges (value : Value Symbol Guard) (shape : NodeShape rowLimit arityLimit value) :
    RowsShape rowLimit arityLimit (InternedEdgeResidency.nodeEdges value) := by
  cases value with
  | empty => trivial
  | node => exact shape.2
  | reference | mu | union => cases shape

/-- Every original node supplies at most the uniform number of alternatives. -/
theorem NodeShape.length (value : Value Symbol Guard) (shape : NodeShape rowLimit arityLimit value) :
    (InternedEdgeResidency.nodeEdges value).length ≤ rowLimit := by
  cases value with
  | empty => exact Nat.zero_le _
  | node => exact shape.1
  | reference | mu | union => cases shape

/-- Each original edge has at most the uniform number of children. -/
theorem EdgeShape.arity (edge : EdgeValue Symbol Guard) (shape : EdgeShape rowLimit arityLimit edge) :
    edge.children.length ≤ arityLimit := by cases edge; exact shape.1

/-- The original ordered children retain all descendant bounds. -/
theorem EdgeShape.children (edge : EdgeValue Symbol Guard) (shape : EdgeShape rowLimit arityLimit edge) :
    ChildrenShape rowLimit arityLimit edge.children := by cases edge; exact shape.2

/-- A literal descendant of an original source row retains both uniform limits. -/
theorem NodeShape.child (value : Value Symbol Guard) (shape : NodeShape rowLimit arityLimit value)
    (edge : EdgeValue Symbol Guard) (present : edge ∈ InternedEdgeResidency.nodeEdges value)
    (child : Value Symbol Guard) (member : child ∈ edge.children) : NodeShape rowLimit arityLimit child :=
  ChildrenShape.member _ (EdgeShape.children edge (RowsShape.member _ (NodeShape.nodeEdges value shape) edge present)) child member

mutual
/-- A uniform node profile contains only the finite ordinary domain. -/
theorem NodeShape.domain (value : Value Symbol Guard) (shape : NodeShape rowLimit arityLimit value) :
    SourceCurrentAllocatedFiniteOrdinaryDomain.Node value := by
  cases value with
  | empty => exact .empty
  | node entry edges depth free => exact .ordinary (RowsShape.domain edges shape.2)
  | reference | mu | union => cases shape
termination_by sizeOf value

/-- Every profiled row has finite ordinary children. -/
theorem RowsShape.domain (edges : List (EdgeValue Symbol Guard)) (shape : RowsShape rowLimit arityLimit edges) :
    SourceCurrentAllocatedFiniteOrdinaryDomain.Rows edges := by
  cases edges with
  | nil => exact .nil
  | cons edge rest => exact .cons (EdgeShape.domain edge shape.1) (RowsShape.domain rest shape.2)
termination_by sizeOf edges

/-- An edge profile derives the complete source child domain. -/
theorem EdgeShape.domain (edge : EdgeValue Symbol Guard) (shape : EdgeShape rowLimit arityLimit edge) :
    SourceCurrentAllocatedFiniteOrdinaryDomain.Edge edge := by
  cases edge with
  | mk entry children => exact ChildrenShape.domain children shape.2
termination_by sizeOf edge

/-- Every child in the profile belongs to the finite ordinary domain. -/
theorem ChildrenShape.domain (values : List (Value Symbol Guard)) (shape : ChildrenShape rowLimit arityLimit values) :
    SourceCurrentAllocatedFiniteOrdinaryDomain.Children values := by
  cases values with
  | nil => exact .nil
  | cons value rest => exact .cons (NodeShape.domain value shape.1) (ChildrenShape.domain rest shape.2)
termination_by sizeOf values
end

mutual
/-- The computed original input limits cover every ordinary descendant. -/
theorem node_shape_self (value : Value Symbol Guard) (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node value) :
    NodeShape (limits value).1 (limits value).2 value := by
  cases domain with
  | empty => trivial
  | @ordinary edges entry depth free domain =>
      exact ⟨Nat.le_max_left _ _, RowsShape.mono edges (rows_shape_self edges domain) (Nat.le_max_right _ _) (Nat.le_refl _)⟩
termination_by sizeOf value

/-- Computed maxima cover every original row occurrence. -/
theorem rows_shape_self (edges : List (EdgeValue Symbol Guard)) (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Rows edges) :
    RowsShape (rowsLimits edges).1 (rowsLimits edges).2 edges := by
  cases domain with
  | nil => trivial
  | @cons rest edge first tail =>
      exact ⟨EdgeShape.mono edge (edge_shape_self edge first) (Nat.le_max_left _ _) (Nat.le_max_left _ _),
        RowsShape.mono rest (rows_shape_self rest tail) (Nat.le_max_right _ _) (Nat.le_max_right _ _)⟩
termination_by sizeOf edges

/-- The original edge arity and all child profiles fit its computed limits. -/
theorem edge_shape_self (edge : EdgeValue Symbol Guard) (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Edge edge) :
    EdgeShape (edgeLimits edge).1 (edgeLimits edge).2 edge := by
  cases edge with
  | mk entry children =>
      exact ⟨Nat.le_max_left _ _, ChildrenShape.mono children (children_shape_self children domain)
        (Nat.le_refl _) (Nat.le_max_right _ _)⟩
termination_by sizeOf edge

/-- A finite root inventory has computed uniform limits for every root and descendant. -/
theorem children_shape_self (values : List (Value Symbol Guard)) (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Children values) :
    ChildrenShape (childrenLimits values).1 (childrenLimits values).2 values := by
  cases domain with
  | nil => trivial
  | @cons value rest first tail =>
      exact ⟨NodeShape.mono value (node_shape_self value first) (Nat.le_max_left _ _) (Nat.le_max_left _ _),
        ChildrenShape.mono rest (children_shape_self rest tail) (Nat.le_max_right _ _) (Nat.le_max_right _ _)⟩
termination_by sizeOf values
end

/-- All roots in the original inventory use the same computed envelope. -/
theorem node_shape_of_root (values : List (Value Symbol Guard)) (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Children values)
    (value : Value Symbol Guard) (member : value ∈ values) :
    NodeShape (childrenLimits values).1 (childrenLimits values).2 value :=
  ChildrenShape.member values (children_shape_self values domain) value member

/-- Equal-symbol joining emits at most one pair per ordered source occurrence pair. -/
theorem pairs_length_le [DecidableEq Symbol] (left right : List (EdgeValue Symbol Guard)) :
    (SourceRecursiveIntersectionKernel.pairs left right).length ≤ left.length * right.length := by
  rw [SourceRecursiveIntersectionKernel.pairs, SymbolicHashJoin.hashJoin_length]
  induction left with
  | nil => simp
  | cons first rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have bounded := Nat.add_le_add (List.length_filter_le (fun second => decide (first.entry.key.symbol = second.entry.key.symbol)) right) ih
      omega

/-- Both profiled operands give a uniform square bound for the literal source join. -/
theorem pairs_length_bound [DecidableEq Symbol] (left right : Value Symbol Guard)
    (leftShape : NodeShape rowLimit arityLimit left) (rightShape : NodeShape rowLimit arityLimit right) :
    (SourceRecursiveIntersectionKernel.pairs (InternedEdgeResidency.nodeEdges left)
      (InternedEdgeResidency.nodeEdges right)).length ≤ rowLimit * rowLimit :=
  Nat.le_trans (pairs_length_le _ _)
    (Nat.mul_le_mul (NodeShape.length left leftShape) (NodeShape.length right rightShape))

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeProfile
