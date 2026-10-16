import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryKeys
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstruction

namespace MicroCFTA.FiniteOrdinaryKeyKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedFiniteOrdinaryKeys

private def literalSyntax : InternedNestedConstruction.Syntax Nat Nat :=
  .node [.mk 8 12 [.node [.mk 7 11 []]]]

private def actualBuild : Value Nat Nat × State Nat Nat :=
  run ((makeEdge 7 11 []).bind fun row =>
    (makeNode [row]).bind fun child =>
      (makeEdge 8 12 [child]).bind fun parent => makeNode [parent]) empty

/-- The literal two-node construction reaches the exact inclusive node supply boundary. -/
theorem actual_constructed_keys :
    actualBuild.2.nodes.next = 2 ∧ Node 1 actualBuild.1 ∧
      SourceRecursiveIntersectionMemo.KeySafe 3 IntersectionEmptyDomain.emptyDomain actualBuild.1 actualBuild.1 := by
  have syntaxDomain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node literalSyntax :=
    .ordinary (.cons (.cons (.ordinary (.cons .nil .nil)) .nil) .nil)
  obtain ⟨value, heap, done, domain, facts, available⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryConstruction.closed literalSyntax syntaxDomain
  have literal : InternedFreshOrdinaryConstruction.build literalSyntax [] empty =
      .done actualBuild.1 actualBuild.2 := by
    simp only [literalSyntax, InternedFreshOrdinaryConstruction.build,
      InternedFreshOrdinaryConstruction.buildEdges, InternedFreshOrdinaryConstruction.buildMany,
      InternedNestedConstruction.Outcome.bind, InternedNestedConstruction.work, actualBuild, run_bind]
  obtain ⟨rfl, rfl⟩ := InternedNestedConstruction.Outcome.done.inj (done.symm.trans literal)
  have counts : actualBuild.2.nodes.next = 2 ∧ actualBuild.2.edges.next = 2 := by
    simp [actualBuild, run_bind, makeEdge, makeNode, surviving, canonicalEdges,
      EnumerationBuilderCaches.canonicalIds, run, edgeStep, nodeStep, Cache.intern,
      Cache.install, Cache.reserve, Cache.keepFirst, Cache.put, empty, Cache.emptyState,
      identifyNode, maximumDepth, childFree, canonicalFree, Value.referenceOf, EdgeValue.children, EdgeValue.entry,
      List.eraseDups_cons]
  have keys := of_available 1 actualBuild.2 facts.coherent facts.linked
    (by rw [counts.1]; decide) (by rw [counts.2]; decide)
    actualBuild.1 available domain
  exact ⟨counts.1, keys, node_key_safe_empty keys keys⟩

/-- Literal joined rows and their paired children inherit the same initial machine bounds. -/
theorem joined_children_keys
    {Symbol Guard : Type} {bits : Nat} {left right : Value Symbol Guard}
    (first : Node bits left) (second : Node bits right)
    {a b : EdgeValue Symbol Guard}
    (leftRow : a ∈ InternedEdgeResidency.nodeEdges left)
    (rightRow : b ∈ InternedEdgeResidency.nodeEdges right)
    {child : Value Symbol Guard × Value Symbol Guard} (member : child ∈ a.children.zip b.children) :
    SourceRecursiveIntersectionEdgeMemo.KeySafe (bits + 2) IntersectionEmptyDomain.emptyDomain a b ∧
      SourceRecursiveIntersectionMemo.KeySafe (bits + 2) IntersectionEmptyDomain.emptyDomain child.1 child.2 := by
  have aKeys := first.nodeEdges.member a leftRow
  have bKeys := second.nodeEdges.member b rightRow
  have inside := List.of_mem_zip member
  exact ⟨edge_key_safe_empty aKeys bKeys,
    node_key_safe_empty (aKeys.2.member child.1 inside.1) (bKeys.2.member child.2 inside.2)⟩

/-- The final ordinary node slot is safe, and the next node identity repeats the first packed key. -/
theorem exact_node_boundary :
    IntersectionFlatMemoKey.Safe 4 (.node 3) ∧
      IntersectionFlatMemoKey.machine 4 (.node 4) = IntersectionFlatMemoKey.machine 4 (.node 0) := by
  exact ⟨(IntersectionFlatMemoKey.safe_range 2 3).1.mpr (by decide),
    IntersectionFlatMemoKey.node_wrap_collision 2⟩

/-- Reset and swap use the same actual recursive input certificates. -/
theorem reset_and_swap
    {Symbol Guard : Type} {bits : Nat} {left right : Value Symbol Guard}
    (first : Node bits left) (second : Node bits right)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (bounded : domain.identity < 2 ^ (bits + 1)) :
    SourceRecursiveIntersectionMemo.KeySafe (bits + 2) domain right left ∧
      SourceRecursiveIntersectionMemo.KeySafe (bits + 2) IntersectionEmptyDomain.emptyDomain left right :=
  ⟨node_key_safe_swap domain bounded first second, node_key_safe_empty first second⟩

#print axioms actual_constructed_keys
#check @actual_constructed_keys
#print axioms joined_children_keys
#check @joined_children_keys
#print axioms exact_node_boundary
#check @exact_node_boundary
#print axioms reset_and_swap
#check @reset_and_swap

end MicroCFTA.FiniteOrdinaryKeyKernels
