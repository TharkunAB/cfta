import MicroCFTA.SourceRecursiveIntersectionCompileMuBounds
import MicroCFTA.SourceRecursiveIntersectionCompileWalkBounds

/-!
# Strict bounds of original union and row requests

Actual branch selection and coherent source readback identify each requested
original member or row. The semantic child decrease supplies its strict
body bound. Original scope is derived from the actual parent payloads.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCode
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionSchedule SourceRecursiveIntersectionRequestProgress

/-- Actual original node children inherit strict request limits from their selected physical branch. -/
theorem node_child_below [DecidableEq Symbol] (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (parent child : NodeRequest Symbol Guard) (scope : NodeScope source parent)
    (complete : Completes (view source holds) (nodeSemantic parent)) (childScope : NodeScope source child)
    (member : nodeSemantic child ∈ branchCalls (view source holds) (SourceRecursiveIntersectionSchedule.domain parent.domain.key)
      (inputOf parent.left) (inputOf parent.right) (decision parent.domain.key parent.left parent.right)) :
    NodeBelow source holds (requiredFuel (view source holds) (nodeSemantic parent) complete) child :=
  ⟨childScope, physical_child_requiredFuel source facts holds parent.domain.key parent.left parent.right
    scope.left scope.right scope.leftAvailable scope.rightAvailable complete _ member⟩

/-- Actual original row children inherit strict request limits from their selected physical branch. -/
theorem edge_child_below [DecidableEq Symbol] (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (parent : NodeRequest Symbol Guard) (child : EdgeRequest Symbol Guard)
    (scope : NodeScope source parent) (complete : Completes (view source holds) (nodeSemantic parent)) (childScope : EdgeScope source child)
    (member : edgeSemantic holds child ∈ branchCalls (view source holds) (SourceRecursiveIntersectionSchedule.domain parent.domain.key)
      (inputOf parent.left) (inputOf parent.right) (decision parent.domain.key parent.left parent.right)) :
    EdgeBelow source holds (requiredFuel (view source holds) (nodeSemantic parent) complete) child :=
  ⟨childScope, physical_child_requiredFuel source facts holds parent.domain.key parent.left parent.right
    scope.left scope.right scope.leftAvailable scope.rightAvailable complete _ member⟩

/-- Each actual left union member derives original scope and a strict parent-body bound. -/
theorem leftUnion_member_below [DecidableEq Symbol] (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (domain : Interned DomainKey) (entry : Interned NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference) (right : Value Symbol Guard)
    (scope : NodeScope source ⟨domain, .union entry members depth free, right⟩)
    (complete : Completes (view source holds) (nodeSemantic ⟨domain, .union entry members depth free, right⟩))
    (selected : decision domain.key (.union entry members depth free) right = .leftUnion) (child : Value Symbol Guard) (member : child ∈ members) :
    NodeBelow source holds (requiredFuel (view source holds) (nodeSemantic ⟨domain, .union entry members depth free, right⟩) complete)
      ⟨domain, child, right⟩ := by
  apply node_child_below source facts holds _ _ scope complete (scope.leftUnion source domain entry members depth free right child member)
  simp only [selected, branchCalls, nodeSemantic, inputOf, Value.referenceOf, IntersectionFlatMemoKey.input, Option.getD_some]
  rw [members_readback source facts holds entry members depth free scope.leftAvailable]
  exact List.mem_map.mpr ⟨inputOf child, List.mem_map.mpr ⟨child, member, rfl⟩, rfl⟩

/-- Each actual right union member derives original scope and a strict parent-body bound. -/
theorem rightUnion_member_below [DecidableEq Symbol] (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (domain : Interned DomainKey) (left : Value Symbol Guard) (entry : Interned NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (scope : NodeScope source ⟨domain, left, .union entry members depth free⟩)
    (complete : Completes (view source holds) (nodeSemantic ⟨domain, left, .union entry members depth free⟩))
    (selected : decision domain.key left (.union entry members depth free) = .rightUnion) (child : Value Symbol Guard) (member : child ∈ members) :
    NodeBelow source holds (requiredFuel (view source holds) (nodeSemantic ⟨domain, left, .union entry members depth free⟩) complete)
      ⟨domain, left, child⟩ := by
  apply node_child_below source facts holds _ _ scope complete (scope.rightUnion source domain left entry members depth free child member)
  simp only [selected, branchCalls, nodeSemantic, inputOf, Value.referenceOf, IntersectionFlatMemoKey.input, Option.getD_some]
  rw [members_readback source facts holds entry members depth free scope.rightAvailable]
  exact List.mem_map.mpr ⟨inputOf child, List.mem_map.mpr ⟨child, member, rfl⟩, rfl⟩

/-- Every actual equal-symbol row pair derives original scope and a strict parent-body bound. -/
theorem rows_member_below [DecidableEq Symbol] (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (domain : Interned DomainKey)
    (first : Interned NodeKey) (leftEdges : List (EdgeValue Symbol Guard)) (leftDepth : Nat) (leftFree : List Reference)
    (second : Interned NodeKey) (rightEdges : List (EdgeValue Symbol Guard)) (rightDepth : Nat) (rightFree : List Reference)
    (scope : NodeScope source ⟨domain, .node first leftEdges leftDepth leftFree, .node second rightEdges rightDepth rightFree⟩)
    (complete : Completes (view source holds) (nodeSemantic ⟨domain, .node first leftEdges leftDepth leftFree, .node second rightEdges rightDepth rightFree⟩))
    (selected : decision domain.key (.node first leftEdges leftDepth leftFree) (.node second rightEdges rightDepth rightFree) = .ordinary)
    (rows : EdgeValue Symbol Guard × EdgeValue Symbol Guard) (member : rows ∈ pairs leftEdges rightEdges) :
    EdgeBelow source holds (requiredFuel (view source holds)
      (nodeSemantic ⟨domain, .node first leftEdges leftDepth leftFree, .node second rightEdges rightDepth rightFree⟩) complete) ⟨domain, rows.1, rows.2⟩ := by
  obtain ⟨leftMember, rightMember, same⟩ := (pairs_member leftEdges rightEdges rows).mp member
  apply edge_child_below source facts holds _ _ scope complete
    (scope.rows source facts domain first leftEdges leftDepth leftFree second rightEdges rightDepth rightFree rows.1 rows.2 leftMember rightMember)
  simp only [selected, branchCalls, edgeSemantic, inputOf, Value.referenceOf, IntersectionFlatMemoKey.input, Option.getD_some]
  rw [rows_readback source facts holds first leftEdges leftDepth leftFree scope.leftAvailable,
    rows_readback source facts holds second rightEdges rightDepth rightFree scope.rightAvailable]
  apply List.mem_map.mpr
  refine ⟨(row holds rows.1, row holds rows.2), ?_, rfl⟩
  apply (SymbolicHashJoin.hashJoin_member _ _ _ _ _).mpr
  exact ⟨row holds rows.1, List.mem_map.mpr ⟨rows.1, leftMember, rfl⟩,
    row holds rows.2, List.mem_map.mpr ⟨rows.2, rightMember, rfl⟩, same, rfl⟩

end MicroCFTA.SourceRecursiveIntersectionCode
