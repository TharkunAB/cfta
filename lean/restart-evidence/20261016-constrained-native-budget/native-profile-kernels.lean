import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeProfile
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstruction

namespace MicroCFTA.NativeProfileKernels
open Cache InternedConstructorTemplates
open InternedBinderProtocol (NodeKey Reference)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile

private def leaf : Value Nat Nat := .node ⟨1, .node []⟩ [] 73 [.interned 19]
private def row : EdgeValue Nat Nat := .mk ⟨2, ⟨7, [.node 1, .empty], 91⟩⟩ [leaf, .empty]
private def middle : Value Nat Nat := .node ⟨3, .node [2, 2, 2]⟩ [row, row, row] 99 [.interned 21]
private def rootRow : EdgeValue Nat Nat := .mk ⟨4, ⟨8, [.node 3], 92⟩⟩ [middle]
private def root : Value Nat Nat := .node ⟨5, .node [4]⟩ [rootRow] 105 [.interned 22]

/-- A deeper wider record controls the envelope despite unrestricted stored metadata. -/
theorem nested_inventory_profile :
    limits root = (3, 2) ∧ NodeShape 3 2 root ∧ NodeShape 3 2 leaf := by
  have leafDomain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node leaf := .ordinary .nil
  have rowDomain : SourceCurrentAllocatedFiniteOrdinaryDomain.Edge row := .cons leafDomain (.cons .empty .nil)
  have middleDomain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node middle := .ordinary (.cons rowDomain (.cons rowDomain (.cons rowDomain .nil)))
  have rootDomain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node root := .ordinary (.cons (.cons middleDomain .nil) .nil)
  have exactLimits : limits root = (3, 2) := rfl
  have profile : NodeShape 3 2 root := by simpa only [exactLimits] using node_shape_self root rootDomain
  have deep := NodeShape.child root profile rootRow (by simp [root, InternedEdgeResidency.nodeEdges]) middle (by simp [rootRow, EdgeValue.children])
  have final := NodeShape.child middle deep row (by simp [middle, InternedEdgeResidency.nodeEdges]) leaf (by simp [row, EdgeValue.children])
  exact ⟨exactLimits, profile, final⟩

/-- Duplicate source occurrences remain in the literal equal-symbol join. -/
theorem duplicate_pairs_count :
    (SourceRecursiveIntersectionKernel.pairs [row, row] [row, row]).length = 4 ∧
      (SourceRecursiveIntersectionKernel.pairs [row, row] [row, row]).length ≤ 2 * 2 := by
  exact ⟨by decide, pairs_length_le [row, row] [row, row]⟩

/-- Joined original rows pass the uniform envelope to every zipped child request. -/
theorem joined_child_profiles {Symbol Guard : Type} [DecidableEq Symbol]
    {rows arity : Nat} {left right : Value Symbol Guard}
    (first : NodeShape rows arity left) (second : NodeShape rows arity right)
    {a b : EdgeValue Symbol Guard}
    (leftRow : a ∈ InternedEdgeResidency.nodeEdges left)
    (rightRow : b ∈ InternedEdgeResidency.nodeEdges right)
    {child : Value Symbol Guard × Value Symbol Guard} (member : child ∈ a.children.zip b.children) :
    (SourceRecursiveIntersectionKernel.pairs (InternedEdgeResidency.nodeEdges left)
      (InternedEdgeResidency.nodeEdges right)).length ≤ rows * rows ∧
      a.children.length ≤ arity ∧ b.children.length ≤ arity ∧
      NodeShape rows arity child.1 ∧ NodeShape rows arity child.2 := by
  have aShape := RowsShape.member _ (NodeShape.nodeEdges left first) a leftRow
  have bShape := RowsShape.member _ (NodeShape.nodeEdges right second) b rightRow
  have inside := List.of_mem_zip member
  exact ⟨pairs_length_bound left right first second, EdgeShape.arity a aShape, EdgeShape.arity b bShape,
    ChildrenShape.member _ (EdgeShape.children a aShape) child.1 inside.1, ChildrenShape.member _ (EdgeShape.children b bShape) child.2 inside.2⟩

/-- Repeated roots share computed maxima, and either limit can increase independently. -/
theorem repeated_roots_common_profile :
    childrenLimits [root, leaf, root] = (3, 2) ∧
      NodeShape 4 7 root ∧ NodeShape 4 7 leaf := by
  obtain ⟨exactLimits, rootShape, leafShape⟩ := nested_inventory_profile
  exact ⟨rfl, NodeShape.mono root rootShape (by decide) (by decide), NodeShape.mono leaf leafShape (by decide) (by decide)⟩

/-- A source constructor obtains its own completed record and computed descendant limits. -/
theorem constructed_profile
    {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (ordinary : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression) :
    ∃ value heap,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap ∧
      SourceCurrentAllocatedFiniteOrdinaryDomain.Node value ∧ NodeShape (limits value).1 (limits value).2 value := by
  obtain ⟨value, heap, built, domain, _, _⟩ := SourceCurrentAllocatedFiniteOrdinaryConstruction.closed expression ordinary
  exact ⟨value, heap, built, domain, node_shape_self value domain⟩

#print axioms nested_inventory_profile
#check @nested_inventory_profile
#print axioms duplicate_pairs_count
#check @duplicate_pairs_count
#print axioms joined_child_profiles
#check @joined_child_profiles
#print axioms repeated_roots_common_profile
#check @repeated_roots_common_profile
#print axioms constructed_profile
#check @constructed_profile
end MicroCFTA.NativeProfileKernels
