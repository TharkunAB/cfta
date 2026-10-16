import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardLimits
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain

/-!
# Hereditary raw guard profiles

Every literal ordinary row and child retains one common raw guard envelope.
Empty values have no guard obligation.
Mu, references, and explicit unions remain outside this profile.
Computed limits visit all initial row and child occurrences.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardProfiles
open Cache InternedConstructorTemplates
open InternedBinderProtocol (NodeKey Reference)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits Bounds)
open SourceCurrentAllocatedFiniteOrdinaryGuardLimits (Le join zero)
variable {Symbol Formula : Type}
local notation "Constraint" => SourceSymbolicIndex.Constraint Formula

mutual
/-- Every raw constraint below an ordinary node satisfies the same limits. -/
def Node (limits : Limits) : Value Symbol Constraint → Prop
  | .empty => True
  | .node _ edges _ _ => Rows limits edges
  | _ => False

/-- Every ordered row retains its literal raw field and descendant profiles. -/
def Rows (limits : Limits) : List (EdgeValue Symbol Constraint) → Prop
  | [] => True
  | edge :: rest => Edge limits edge ∧ Rows limits rest

/-- An edge retains the raw stored equality and guard envelope as well as its children. -/
def Edge (limits : Limits) : EdgeValue Symbol Constraint → Prop
  | .mk entry children => Bounds limits entry.key.constraint ∧ Children limits children

/-- Every ordered child retains the complete hereditary profile. -/
def Children (limits : Limits) : List (Value Symbol Constraint) → Prop
  | [] => True
  | value :: rest => Node limits value ∧ Children limits rest
end

/-- Empty contributes no raw guard. -/
theorem Node.empty (limits : Limits) : Node limits (.empty : Value Symbol Constraint) := trivial

/-- A literal ordinary node retains the complete row profile. -/
theorem Node.ordinary (limits : Limits) (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List Reference) (profile : Rows limits edges) : Node limits (.node entry edges depth free) := profile

/-- The empty row list retains every common envelope. -/
theorem Rows.nil (limits : Limits) : Rows limits ([] : List (EdgeValue Symbol Constraint)) := trivial

/-- Ordered row construction preserves both actual component profiles. -/
theorem Rows.cons {limits : Limits} {edge : EdgeValue Symbol Constraint} {edges : List (EdgeValue Symbol Constraint)}
    (first : Edge limits edge) (rest : Rows limits edges) : Rows limits (edge :: edges) := ⟨first, rest⟩

/-- A literal edge keeps its own raw field bound and complete child profile. -/
theorem Edge.mk (limits : Limits) (entry : Interned (EdgeKey Symbol Constraint)) (children : List (Value Symbol Constraint))
    (guard : Bounds limits entry.key.constraint) (profile : Children limits children) : Edge limits (.mk entry children) :=
  ⟨guard, profile⟩

/-- The empty forest has no raw guard obligation. -/
theorem Children.nil (limits : Limits) : Children limits ([] : List (Value Symbol Constraint)) := trivial

/-- Ordered child construction preserves the exact component profiles. -/
theorem Children.cons {limits : Limits} {value : Value Symbol Constraint} {values : List (Value Symbol Constraint)}
    (first : Node limits value) (rest : Children limits values) : Children limits (value :: values) := ⟨first, rest⟩

mutual
/-- Increasing the raw envelope retains the complete node profile. -/
theorem Node.mono (value : Value Symbol Constraint) {first last : Limits} (profile : Node first value)
    (enough : Le first last) : Node last value := by
  cases value with
  | empty => trivial
  | node entry edges depth free => exact Rows.mono edges profile enough
  | reference | mu | union => cases profile
termination_by sizeOf value

/-- Increasing the raw envelope retains every row occurrence. -/
theorem Rows.mono (edges : List (EdgeValue Symbol Constraint)) {first last : Limits} (profile : Rows first edges)
    (enough : Le first last) : Rows last edges := by
  cases edges with
  | nil => trivial
  | cons edge rest => exact ⟨Edge.mono edge profile.1 enough, Rows.mono rest profile.2 enough⟩
termination_by sizeOf edges

/-- Increasing the raw envelope retains the own field and all descendant bounds. -/
theorem Edge.mono (edge : EdgeValue Symbol Constraint) {first last : Limits} (profile : Edge first edge)
    (enough : Le first last) : Edge last edge := by
  cases edge with
  | mk entry children => exact ⟨SourceCurrentAllocatedFiniteOrdinaryGuardLimits.bounds_mono _ profile.1 enough,
      Children.mono children profile.2 enough⟩
termination_by sizeOf edge

/-- Increasing the raw envelope retains every ordered child occurrence. -/
theorem Children.mono (values : List (Value Symbol Constraint)) {first last : Limits} (profile : Children first values)
    (enough : Le first last) : Children last values := by
  cases values with
  | nil => trivial
  | cons value rest => exact ⟨Node.mono value profile.1 enough, Children.mono rest profile.2 enough⟩
termination_by sizeOf values
end

/-- A selected original row retains its literal own field and complete descendants. -/
theorem Rows.member (edges : List (EdgeValue Symbol Constraint)) {limits : Limits} (profile : Rows limits edges)
    (edge : EdgeValue Symbol Constraint) (member : edge ∈ edges) : Edge limits edge := by
  induction edges with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact profile.1
      · exact ih profile.2 member

/-- A selected original child retains the same hereditary envelope. -/
theorem Children.member (values : List (Value Symbol Constraint)) {limits : Limits} (profile : Children limits values)
    (value : Value Symbol Constraint) (member : value ∈ values) : Node limits value := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact profile.1
      · exact ih profile.2 member

/-- Pointwise exact row profiles construct the ordered row predicate. -/
theorem rows_of_members (limits : Limits) (edges : List (EdgeValue Symbol Constraint))
    (profiles : ∀ edge ∈ edges, Edge limits edge) : Rows limits edges := by
  induction edges with
  | nil => trivial
  | cons first rest ih => exact ⟨profiles first List.mem_cons_self,
      ih (fun edge member => profiles edge (List.mem_cons_of_mem first member))⟩

/-- Pointwise exact child profiles construct the ordered forest predicate. -/
theorem children_of_members (limits : Limits) (values : List (Value Symbol Constraint))
    (profiles : ∀ value ∈ values, Node limits value) : Children limits values := by
  induction values with
  | nil => trivial
  | cons first rest ih => exact ⟨profiles first List.mem_cons_self,
      ih (fun value member => profiles value (List.mem_cons_of_mem first member))⟩

/-- Ordinary row readback exposes the same original row list. -/
theorem Node.rows (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List Reference)
    {limits : Limits} (profile : Node limits (.node entry edges depth free)) : Rows limits edges := profile

/-- Empty and ordinary values expose only hereditarily profiled rows. -/
theorem Node.nodeEdges (value : Value Symbol Constraint) {limits : Limits} (profile : Node limits value) :
    Rows limits (InternedEdgeResidency.nodeEdges value) := by
  cases value with
  | empty => trivial
  | node => exact profile
  | reference | mu | union => cases profile

/-- Each original edge exposes the exact raw key constraint bound. -/
theorem Edge.guard (edge : EdgeValue Symbol Constraint) {limits : Limits} (profile : Edge limits edge) :
    Bounds limits edge.entry.key.constraint := by cases edge; exact profile.1

/-- Each original edge exposes its exact ordered child profile. -/
theorem Edge.children (edge : EdgeValue Symbol Constraint) {limits : Limits} (profile : Edge limits edge) :
    Children limits edge.children := by cases edge; exact profile.2

/-- A literal ordinary descendant retains the complete original envelope. -/
theorem Node.child (value : Value Symbol Constraint) {limits : Limits} (profile : Node limits value)
    (edge : EdgeValue Symbol Constraint) (present : edge ∈ InternedEdgeResidency.nodeEdges value)
    (child : Value Symbol Constraint) (member : child ∈ edge.children) : Node limits child :=
  Children.member _ (Edge.children edge (Rows.member _ (Node.nodeEdges value profile) edge present)) child member

mutual
/-- Hereditary raw guard profiles admit only finite ordinary nodes. -/
theorem Node.domain (value : Value Symbol Constraint) {limits : Limits} (profile : Node limits value) :
    SourceCurrentAllocatedFiniteOrdinaryDomain.Node value := by
  cases value with
  | empty => exact .empty
  | node entry edges depth free => exact .ordinary (Rows.domain edges profile)
  | reference | mu | union => cases profile
termination_by sizeOf value

/-- Every profiled row has finite ordinary children. -/
theorem Rows.domain (edges : List (EdgeValue Symbol Constraint)) {limits : Limits} (profile : Rows limits edges) :
    SourceCurrentAllocatedFiniteOrdinaryDomain.Rows edges := by
  cases edges with
  | nil => exact .nil
  | cons edge rest => exact .cons (Edge.domain edge profile.1) (Rows.domain rest profile.2)
termination_by sizeOf edges

/-- A profiled edge has finite ordinary children without restricting its raw guard syntax. -/
theorem Edge.domain (edge : EdgeValue Symbol Constraint) {limits : Limits} (profile : Edge limits edge) :
    SourceCurrentAllocatedFiniteOrdinaryDomain.Edge edge := by
  cases edge with
  | mk entry children => exact Children.domain children profile.2
termination_by sizeOf edge

/-- Every profiled forest consists of finite ordinary values. -/
theorem Children.domain (values : List (Value Symbol Constraint)) {limits : Limits} (profile : Children limits values) :
    SourceCurrentAllocatedFiniteOrdinaryDomain.Children values := by
  cases values with
  | nil => exact .nil
  | cons value rest => exact .cons (Node.domain value profile.1) (Children.domain rest profile.2)
termination_by sizeOf values
end

mutual
/-- Initial node limits include every literal nested raw constraint. -/
def limits : Value Symbol Constraint → Limits
  | .node _ edges _ _ => rowsLimits edges
  | _ => zero

/-- Every original row occurrence contributes to the common envelope. -/
def rowsLimits : List (EdgeValue Symbol Constraint) → Limits
  | [] => zero
  | edge :: rest => join (edgeLimits edge) (rowsLimits rest)

/-- The original raw own field and every child contribute to the same envelope. -/
def edgeLimits : EdgeValue Symbol Constraint → Limits
  | .mk entry children => join (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.of_constraint entry.key.constraint) (childrenLimits children)

/-- Every original root and descendant occurrence contributes to the common envelope. -/
def childrenLimits : List (Value Symbol Constraint) → Limits
  | [] => zero
  | value :: rest => join (limits value) (childrenLimits rest)
end

mutual
/-- A finite ordinary node fits its directly computed initial raw envelope. -/
theorem node_self (value : Value Symbol Constraint) (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node value) :
    Node (limits value) value := by
  cases domain with
  | empty => trivial
  | @ordinary edges entry depth free domain => exact rows_self edges domain
termination_by sizeOf value

/-- A finite row list fits its directly computed initial raw envelope. -/
theorem rows_self (edges : List (EdgeValue Symbol Constraint)) (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Rows edges) :
    Rows (rowsLimits edges) edges := by
  cases domain with
  | nil => trivial
  | @cons rest edge first tail => exact ⟨Edge.mono edge (edge_self edge first)
      (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.le_join_left _ _),
    Rows.mono rest (rows_self rest tail) (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.le_join_right _ _)⟩
termination_by sizeOf edges

/-- A finite original edge fits its own stored-field, raw-guard, and descendant maxima. -/
theorem edge_self (edge : EdgeValue Symbol Constraint) (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Edge edge) :
    Edge (edgeLimits edge) edge := by
  cases edge with
  | mk entry children => exact ⟨SourceCurrentAllocatedFiniteOrdinaryGuardLimits.bounds_mono _
      (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.of_constraint_bounds entry.key.constraint)
      (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.le_join_left _ _),
    Children.mono children (children_self children domain) (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.le_join_right _ _)⟩
termination_by sizeOf edge

/-- A finite original forest fits a single computed initial raw envelope. -/
theorem children_self (values : List (Value Symbol Constraint)) (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Children values) :
    Children (childrenLimits values) values := by
  cases domain with
  | nil => trivial
  | @cons value rest first tail => exact ⟨Node.mono value (node_self value first)
      (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.le_join_left _ _),
    Children.mono rest (children_self rest tail) (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.le_join_right _ _)⟩
termination_by sizeOf values
end

/-- Every initial root uses the same computed hereditary envelope. -/
theorem node_of_root (values : List (Value Symbol Constraint)) (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Children values)
    (value : Value Symbol Constraint) (member : value ∈ values) : Node (childrenLimits values) value :=
  Children.member values (children_self values domain) value member

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardProfiles
