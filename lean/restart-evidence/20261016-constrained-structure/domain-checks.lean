import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain
import MicroCFTA.SourceEqualityConstraintConstructors

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Node
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Node
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Node.empty
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Node.empty
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Node.ordinary
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Node.ordinary
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Rows.nil
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Rows.nil
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Rows.cons
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Rows.cons
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Children
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Children
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Children.nil
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Children.nil
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Children.cons
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Children.cons
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Children.member
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Children.member
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Children.of_members
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Children.of_members
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Rows.member
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Rows.member
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Rows.of_members
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Rows.of_members
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Node.rows
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Node.rows
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Node.nodeEdges
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Node.nodeEdges
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Node.child
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Node.child
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.not_reference
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.not_reference
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.not_mu
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.not_mu
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.not_union
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.not_union
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Node.child_lt
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.Node.child_lt
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.edgeHeight_children
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.edgeHeight_children
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.child_le_edge
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.child_le_edge
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge_bound
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge_bound
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.ordinaryUnion
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.ordinaryUnion
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode_bound
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode_bound
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.ordinaryUnion_bound
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain.ordinaryUnion_bound

namespace DomainChecks
open MicroCFTA
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open InternedFreshProbeKeys
open MergedOrdinaryHeight (height edgeHeight)

/-- The structural domain permits a nonempty source equality class. -/
theorem full_equalities (symbol : Symbol) (guard : SourceGuards.Guard Formula) :
    let constraint : SourceSymbolicIndex.Constraint Formula := ⟨some [[[0], [1]]], guard⟩
    let edge : EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula) :=
      .mk ⟨0, ⟨symbol, [.empty, .empty], constraint⟩⟩ [.empty, .empty]
    SourceCurrentAllocatedFiniteOrdinaryDomain.Node (.node ⟨0, .node [0]⟩ [edge] 0 []) ∧ constraint.equalities = some [[[0], [1]]] := by
  exact ⟨.ordinary (.cons (.cons .empty (.cons .empty .nil)) .nil), rfl⟩

/-- Pure structure does not validate a cached free-name field. -/
theorem metadata_boundary :
    ∃ value : Value Nat Nat, SourceCurrentAllocatedFiniteOrdinaryDomain.Node value ∧ value.free ≠ [] := by
  exact ⟨.node ⟨0, .node []⟩ [] 0 [.interned 1], .ordinary .nil, by decide⟩

variable {Symbol Guard : Type}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual edge allocation and its returned-state node allocation retain the domain and bound. -/
theorem edge_then_node
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state) (linked : Linked state)
    (available : ∀ value ∈ values, Available state value) (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Children values)
    (bound : Nat) (bounded : ∀ value ∈ values, height value ≤ bound) :
    let built := run (InternedConstructorTemplates.makeEdge symbol guard values) state
    let result := (run (InternedConstructorTemplates.makeNode [built.1]) built.2).1
    SourceCurrentAllocatedFiniteOrdinaryDomain.Node result ∧ height result ≤ bound + 1 := by
  let built := run (InternedConstructorTemplates.makeEdge symbol guard values) state
  have physical := makeEdge_available symbol guard values state coherent cached available
  have stored := makeEdge_linked symbol guard values state coherent linked
  have rowDomain := SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge symbol guard values state coherent cached available domain
  have rowBound : edgeHeight built.1 ≤ bound := SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge_bound symbol guard values state coherent cached available bound bounded
  have resident : ∀ edge ∈ [built.1], EdgeResident built.2 edge := by
    intro edge member
    cases List.mem_singleton.mp member
    exact stored.2
  exact ⟨SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode [built.1] built.2 physical.1 stored.1 resident (.cons rowDomain .nil),
    SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode_bound [built.1] built.2 physical.1 stored.1 resident (bound + 1) (by
      intro edge member
      cases List.mem_singleton.mp member
      omega)⟩

/-- Each operand can supply its own independent bound for one actual constructed row. -/
theorem constructed_row_below_each
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state)
    (available : ∀ value ∈ values, Available state value) (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Children values)
    (left right : EdgeValue Symbol Guard)
    (leftBound : ∀ value ∈ values, height value ≤ edgeHeight left)
    (rightBound : ∀ value ∈ values, height value ≤ edgeHeight right) :
    let result := (run (InternedConstructorTemplates.makeEdge symbol guard values) state).1
    SourceCurrentAllocatedFiniteOrdinaryDomain.Edge result ∧ edgeHeight result ≤ edgeHeight left ∧ edgeHeight result ≤ edgeHeight right :=
  ⟨SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge symbol guard values state coherent cached available domain,
    SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge_bound symbol guard values state coherent cached available _ leftBound,
    SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge_bound symbol guard values state coherent cached available _ rightBound⟩

/-- An ordinary union returns a domain value rather than an explicit union record. -/
theorem ordinary_union_excludes_explicit_union
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ value ∈ values, Resident state value) (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Children values)
    (bound : Nat) (bounded : ∀ value ∈ values, height value ≤ bound) :
    let result := (run (MergedOrdinaryHeight.ordinaryUnion values) state).1
    SourceCurrentAllocatedFiniteOrdinaryDomain.Node result ∧ height result ≤ bound ∧
      ∀ entry members depth free, result ≠ .union entry members depth free := by
  have output := SourceCurrentAllocatedFiniteOrdinaryDomain.ordinaryUnion values state coherent linked resident domain
  refine ⟨output, SourceCurrentAllocatedFiniteOrdinaryDomain.ordinaryUnion_bound values state coherent linked resident bound bounded, ?_⟩
  intro entry members depth free same
  rw [same] at output
  exact SourceCurrentAllocatedFiniteOrdinaryDomain.not_union entry members depth free output

end DomainChecks

#print axioms DomainChecks.full_equalities
#check @DomainChecks.full_equalities
#print axioms DomainChecks.metadata_boundary
#check @DomainChecks.metadata_boundary
#print axioms DomainChecks.edge_then_node
#check @DomainChecks.edge_then_node
#print axioms DomainChecks.constructed_row_below_each
#check @DomainChecks.constructed_row_below_each
#print axioms DomainChecks.ordinary_union_excludes_explicit_union
#check @DomainChecks.ordinary_union_excludes_explicit_union
