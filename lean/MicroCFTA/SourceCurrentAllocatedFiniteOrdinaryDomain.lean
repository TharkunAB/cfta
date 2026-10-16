import MicroCFTA.MergedOrdinaryHeight
import MicroCFTA.InternedShallowValues

/-!
# Finite ordinary structures with unrestricted guards

The domain contains Empty and ordinary nodes. Every row child belongs
to the same domain. Mu, explicit union, and reference records do not
belong to it. Guards and their equality classes have no restriction.
Actual constructor closure uses coherent resident record readback.
No execution from an earlier caller model is transferred.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedRecordCoherence InternedFreshProbeKeys
open MergedOrdinaryHeight (height edgeHeight edgesHeight childrenHeight ordinaryUnion)
variable {Symbol Guard : Type}

mutual
/-- Finite ordinary values retain every actual row child recursively. -/
inductive Node : Value Symbol Guard → Prop where
  | empty : Node .empty
  | ordinary (rows : Rows edges) : Node (.node entry edges depth free)

/-- Each actual row has domain children, with no guard restriction. -/
inductive Rows : List (EdgeValue Symbol Guard) → Prop where
  | nil : Rows []
  | cons (children : Children edge.children) (rest : Rows edges) : Rows (edge :: edges)

/-- An ordered child forest contains only domain values. -/
inductive Children : List (Value Symbol Guard) → Prop where
  | nil : Children []
  | cons (first : Node value) (rest : Children values) : Children (value :: values)
end

/-- The edge domain depends on the complete ordered child records. -/
def Edge (edge : EdgeValue Symbol Guard) : Prop := Children edge.children

/-- Membership in a domain child list gives the complete child domain. -/
theorem Children.member {values : List (Value Symbol Guard)} (domain : Children values)
    (value : Value Symbol Guard) (member : value ∈ values) : Node value := by
  cases domain with
  | nil => cases member
  | cons first rest =>
      rcases List.mem_cons.mp member with same | later
      · exact same ▸ first
      · exact rest.member value later
termination_by values.length

/-- Pointwise domain facts construct the ordered child certificate. -/
theorem Children.of_members (values : List (Value Symbol Guard))
    (domain : ∀ value ∈ values, Node value) : Children values := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      exact .cons (domain value List.mem_cons_self) (ih (fun child member => domain child (List.mem_cons_of_mem _ member)))

/-- Membership in domain rows gives the exact row's complete child domain. -/
theorem Rows.member {edges : List (EdgeValue Symbol Guard)} (domain : Rows edges)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) : Edge edge := by
  cases domain with
  | nil => cases member
  | cons children rest =>
      rcases List.mem_cons.mp member with same | later
      · exact same ▸ children
      · exact rest.member edge later
termination_by edges.length

/-- Pointwise row domains construct the ordered row certificate. -/
theorem Rows.of_members (edges : List (EdgeValue Symbol Guard))
    (domain : ∀ edge ∈ edges, Edge edge) : Rows edges := by
  induction edges with
  | nil => exact .nil
  | cons edge edges ih =>
      exact .cons (domain edge List.mem_cons_self) (ih (fun row member => domain row (List.mem_cons_of_mem _ member)))

/-- The rows of an ordinary domain node retain their original order and payloads. -/
theorem Node.rows {entry : Interned InternedBinderProtocol.NodeKey} {edges : List (EdgeValue Symbol Guard)}
    {depth : Nat} {free : List InternedBinderProtocol.Reference} (domain : Node (.node entry edges depth free)) :
    Rows edges := by cases domain; assumption

/-- Empty and ordinary values both supply their actual outgoing domain rows. -/
theorem Node.nodeEdges {value : Value Symbol Guard} (domain : Node value) : Rows (nodeEdges value) := by
  cases domain with
  | empty => exact .nil
  | ordinary rows => exact rows

/-- Each literal row child of a domain node belongs to the domain. -/
theorem Node.child {value : Value Symbol Guard} (domain : Node value)
    (edge : EdgeValue Symbol Guard) (present : edge ∈ InternedEdgeResidency.nodeEdges value)
    (child : Value Symbol Guard) (member : child ∈ edge.children) : Node child :=
  (domain.nodeEdges.member edge present).member child member

/-- No bare reference belongs to the finite ordinary domain. -/
theorem not_reference (name : InternedBinderProtocol.Reference) :
    ¬ Node (.reference name : Value Symbol Guard) := by intro impossible; cases impossible

/-- No Mu record belongs to the finite ordinary domain. -/
theorem not_mu (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard) :
    ¬ Node (.mu entry body depth ordinary) := by intro impossible; cases impossible

/-- No explicit union record belongs to the finite ordinary domain. -/
theorem not_union (entry : Interned InternedBinderProtocol.NodeKey) (members : List (Value Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) :
    ¬ Node (.union entry members depth free) := by intro impossible; cases impossible

/-- Every literal child is strictly below an ordinary parent in constructor height. -/
theorem Node.child_lt {entry : Interned InternedBinderProtocol.NodeKey} {edges : List (EdgeValue Symbol Guard)}
    {depth : Nat} {free : List InternedBinderProtocol.Reference} (domain : Node (.node entry edges depth free))
    (edge : EdgeValue Symbol Guard) (present : edge ∈ edges)
    (child : Value Symbol Guard) (member : child ∈ edge.children) :
    Node child ∧ height child < height (.node entry edges depth free) :=
  ⟨(domain.rows.member edge present).member child member,
    MergedOrdinaryHeight.child_lt entry edges depth free edge present child member⟩

/-- Complete edge height is exactly the maximum height of its ordered children. -/
theorem edgeHeight_children (edge : EdgeValue Symbol Guard) : edgeHeight edge = childrenHeight edge.children := by
  cases edge
  rfl

/-- A child cannot exceed the height below its containing edge. -/
theorem child_le_edge (edge : EdgeValue Symbol Guard) (child : Value Symbol Guard) (member : child ∈ edge.children) :
    height child ≤ edgeHeight edge := by
  rw [edgeHeight_children]
  exact (MergedOrdinaryHeight.childrenHeight_le _ _).mp (Nat.le_refl _) child member

/-- Raw edge construction accepts arbitrary symbols and guards and retains domain children. -/
theorem makeEdge [DecidableEq (EdgeKey Symbol Guard)]
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state)
    (available : ∀ value ∈ values, Available state value) (domain : Children values) :
    Edge (run (InternedConstructorTemplates.makeEdge symbol guard values) state).1 := by
  change Children (run (InternedConstructorTemplates.makeEdge symbol guard values) state).1.children
  rw [InternedShallowValues.makeEdge_children symbol guard values state coherent cached available]
  exact domain

/-- Exact edge readback gives the child-height bound at the same actual constructor result. -/
theorem makeEdge_bound [DecidableEq (EdgeKey Symbol Guard)]
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state) (available : ∀ value ∈ values, Available state value)
    (bound : Nat) (bounded : ∀ value ∈ values, height value ≤ bound) :
    edgeHeight (run (InternedConstructorTemplates.makeEdge symbol guard values) state).1 ≤ bound := by
  rw [edgeHeight_children, InternedShallowValues.makeEdge_children symbol guard values state coherent cached available]
  exact (MergedOrdinaryHeight.childrenHeight_le values bound).mpr bounded

/-- Node filtering and canonical ordering retain the supplied complete domain rows. -/
theorem makeNode [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state) (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (domain : Rows edges) : Node (run (InternedConstructorTemplates.makeNode edges) state).1 := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have selectedDomain : Rows (canonicalEdges (surviving edges)) :=
    Rows.of_members _ (fun edge member => domain.member edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1)
  unfold InternedConstructorTemplates.makeNode
  dsimp only
  split
  · exact .empty
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback (first :: rest) state coherent linked
      (by simpa only [same] using selected)
    simp only [run, exactResult, identifyNode]
    exact .ordinary (by simpa only [same] using selectedDomain)

/-- Domain ordinary union concatenates actual rows and creates no explicit union record. -/
theorem ordinaryUnion [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ value ∈ values, Resident state value) (domain : Children values) :
    Node (run (MergedOrdinaryHeight.ordinaryUnion values) state).1 := by
  apply makeNode _ state coherent linked
  · intro edge member
    obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
    exact resident_edges state linked value (resident value present) edge included
  · apply Rows.of_members
    intro edge member
    obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
    exact (domain.member value present).nodeEdges.member edge included

/-- Actual normalized node construction respects the maximum height of its supplied rows. -/
theorem makeNode_bound [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state) (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (bound : Nat) (bounded : ∀ edge ∈ edges, edgeHeight edge + 1 ≤ bound) :
    height (run (InternedConstructorTemplates.makeNode edges) state).1 ≤ bound :=
  MergedOrdinaryHeight.makeNode_bound edges state coherent linked resident bound bounded

/-- Actual ordinary union cannot exceed the maximum height of its source operands. -/
theorem ordinaryUnion_bound [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ value ∈ values, Resident state value)
    (bound : Nat) (bounded : ∀ value ∈ values, height value ≤ bound) :
    height (run (MergedOrdinaryHeight.ordinaryUnion values) state).1 ≤ bound :=
  MergedOrdinaryHeight.ordinaryUnion_bound values state coherent linked resident bound bounded

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain
