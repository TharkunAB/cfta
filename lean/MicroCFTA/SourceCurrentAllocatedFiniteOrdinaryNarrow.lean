import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequired
import MicroCFTA.EqualityLeafProjectionRuntimeEmpty

/-!
# Positional finite ordinary narrowing laws

Narrowing retains the result domain and bounds its constructor height.
Ordered forest and row relations retain each original position.
Raw constructors use their actual coherent resident records.
Empty propagation changes no physical state.
These laws do not assert language containment or completed execution.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNarrow
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow EdgeNarrow)
open MergedOrdinaryHeight (height edgeHeight childrenHeight edgesHeight)
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
variable {Symbol Guard : Type}

/-- A domain value retains its own height bound. -/
theorem node_refl {value : Value Symbol Guard} (domain : DNode value) : NodeNarrow value value :=
  ⟨domain, Nat.le_refl _⟩

/-- Consecutive node bounds retain the original input bound. -/
theorem node_trans {value middle result : Value Symbol Guard}
    (first : NodeNarrow value middle) (last : NodeNarrow middle result) : NodeNarrow value result :=
  ⟨last.1, Nat.le_trans last.2 first.2⟩

/-- Empty has no greater height than any original input. -/
theorem node_empty (value : Value Symbol Guard) : NodeNarrow value .empty := ⟨.empty, Nat.zero_le _⟩

/-- An ordered domain forest retains its own positions and bounds. -/
theorem forest_refl {values : List (Value Symbol Guard)} (domain : DChildren values) : All₂ NodeNarrow values values := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      cases domain with
      | cons first rest => exact .cons (node_refl first) (ih rest)

/-- Consecutive positional forest bounds compose in their original order. -/
theorem forest_trans {values middle results : List (Value Symbol Guard)}
    (first : All₂ NodeNarrow values middle) (last : All₂ NodeNarrow middle results) : All₂ NodeNarrow values results := by
  induction first generalizing results with
  | nil => cases last; exact .nil
  | cons first rest ih =>
      cases last with
      | cons next tail => exact .cons (node_trans first next) (ih tail)

/-- Each output occurrence has its own finite ordinary domain. -/
theorem forest_domain {values results : List (Value Symbol Guard)}
    (related : All₂ NodeNarrow values results) : DChildren results := by
  induction related with
  | nil => exact .nil
  | cons first rest ih => exact .cons first.1 ih

/-- Positional bounds also bound the maximum forest height. -/
theorem forest_height {values results : List (Value Symbol Guard)}
    (related : All₂ NodeNarrow values results) : childrenHeight results ≤ childrenHeight values := by
  induction related with
  | nil => exact Nat.le_refl _
  | cons first rest ih => exact Nat.max_le.mpr ⟨Nat.le_trans first.2 (Nat.le_max_left _ _), Nat.le_trans ih (Nat.le_max_right _ _)⟩

/-- A domain row retains its own height bound. -/
theorem edge_refl {edge : EdgeValue Symbol Guard} (domain : DEdge edge) : EdgeNarrow edge edge :=
  ⟨domain, Nat.le_refl _⟩

/-- Consecutive row bounds retain the original row bound. -/
theorem edge_trans {edge middle result : EdgeValue Symbol Guard}
    (first : EdgeNarrow edge middle) (last : EdgeNarrow middle result) : EdgeNarrow edge result :=
  ⟨last.1, Nat.le_trans last.2 first.2⟩

/-- Exact ordered child bounds give the corresponding complete row bound. -/
theorem edge_children {edge result : EdgeValue Symbol Guard}
    (related : All₂ NodeNarrow edge.children result.children) : EdgeNarrow edge result := by
  refine ⟨forest_domain related, ?_⟩
  rw [SourceCurrentAllocatedFiniteOrdinaryDomain.edgeHeight_children, SourceCurrentAllocatedFiniteOrdinaryDomain.edgeHeight_children]
  exact forest_height related

/-- Every original domain row retains its ordered position. -/
theorem rows_refl {edges : List (EdgeValue Symbol Guard)} (domain : DRows edges) : All₂ EdgeNarrow edges edges := by
  induction edges with
  | nil => exact .nil
  | cons edge edges ih =>
      cases domain with
      | cons first rest => exact .cons (edge_refl first) (ih rest)

/-- Consecutive ordered row bounds compose without a set conversion. -/
theorem rows_trans {edges middle results : List (EdgeValue Symbol Guard)}
    (first : All₂ EdgeNarrow edges middle) (last : All₂ EdgeNarrow middle results) : All₂ EdgeNarrow edges results := by
  induction first generalizing results with
  | nil => cases last; exact .nil
  | cons first rest ih =>
      cases last with
      | cons next tail => exact .cons (edge_trans first next) (ih tail)

/-- Ordered row bounds retain every output row's complete domain. -/
theorem rows_domain {edges results : List (EdgeValue Symbol Guard)} (related : All₂ EdgeNarrow edges results) : DRows results := by
  induction related with
  | nil => exact .nil
  | cons first rest ih => exact .cons first.1 ih

/-- Ordered row bounds also bound their maximum edge height. -/
theorem rows_height {edges results : List (EdgeValue Symbol Guard)}
    (related : All₂ EdgeNarrow edges results) : edgesHeight results ≤ edgesHeight edges := by
  induction related with
  | nil => exact Nat.le_refl _
  | cons first rest ih => exact Nat.max_le.mpr ⟨Nat.le_trans first.2 (Nat.le_max_left _ _), Nat.le_trans ih (Nat.le_max_right _ _)⟩

/-- Literal erasure retains the original forest positions with zero output height. -/
theorem forest_erase (values : List (Value Symbol Guard)) : All₂ NodeNarrow values (EqualityLeafProjectionRuntimeEmpty.erase values) := by
  induction values with
  | nil => exact .nil
  | cons value values ih => exact .cons (node_empty value) ih

/-- Actual final propagation retains positional domain and height bounds. -/
theorem forest_propagate {values : List (Value Symbol Guard)} (domain : DChildren values) :
    All₂ NodeNarrow values (EqualityLeafProjectionRuntimeEmpty.propagate values) := by
  unfold EqualityLeafProjectionRuntimeEmpty.propagate
  split
  · exact forest_erase values
  · exact forest_refl domain

/-- Exact raw edge construction retains the original child-height bound. -/
theorem makeEdge [DecidableEq (EdgeKey Symbol Guard)] (original : EdgeValue Symbol Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent state) (cached : Cached state) (available : Values state values)
    (related : All₂ NodeNarrow original.children values) :
    EdgeNarrow original (run (InternedConstructorTemplates.makeEdge original.entry.key.symbol original.entry.key.constraint values) state).1 := by
  have bound : childrenHeight values ≤ edgeHeight original := by
    rw [SourceCurrentAllocatedFiniteOrdinaryDomain.edgeHeight_children]
    exact forest_height related
  exact ⟨SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge _ _ values state coherent cached available (forest_domain related),
    SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge_bound _ _ values state coherent cached available _
      ((MergedOrdinaryHeight.childrenHeight_le _ _).mp bound)⟩

/-- Exact raw node reconstruction retains the original ordinary-node height bound. -/
theorem makeNode [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned InternedBinderProtocol.NodeKey)
    (originals results : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (state : State Symbol Guard) (coherent : InternedRecordCoherence.Coherent state) (linked : Linked state)
    (resident : Edges state results) (related : All₂ EdgeNarrow originals results) :
    NodeNarrow (.node entry originals depth free) (run (InternedConstructorTemplates.makeNode results) state).1 := by
  refine ⟨SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode results state coherent linked resident (rows_domain related), ?_⟩
  apply SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode_bound results state coherent linked resident
  intro edge member
  exact Nat.succ_le_succ (Nat.le_trans
    ((MergedOrdinaryHeight.edgesHeight_le results _).mp (Nat.le_refl _) edge member) (rows_height related))
end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNarrow
