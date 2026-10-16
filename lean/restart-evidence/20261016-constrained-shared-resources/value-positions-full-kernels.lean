import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryValuePositions

namespace MicroCFTA.ValuePositionsKernels
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open SourceCurrentAllocatedFiniteOrdinaryValuePositions
open MergedOrdinaryHeight (height edgeHeight edgesHeight childrenHeight)
local notation "EdgeCount" => SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.edgeCount
variable {Symbol Guard : Type}

theorem empty_forest :
    children ([.empty, .empty] : List (Value Symbol Guard)) = 2 ∧
      (SourceCurrentAllocatedFiniteOrdinaryOccurrences.children ([.empty, .empty] : List (Value Symbol Guard))).1 = 0 ∧
      children ([.empty, .empty] : List (Value Symbol Guard)) ≤ 2 * (1 + 0 * EdgeCount 0 0 0) := by
  have profile : ChildrenShape 0 0 ([.empty, .empty] : List (Value Symbol Guard)) := by
    simp [ChildrenShape, NodeShape]
  exact ⟨rfl, rfl, profile_forest _ profile 2 0 (by simp) (by simp [childrenHeight, height])⟩

theorem repeated_row (entry : Interned InternedBinderProtocol.NodeKey)
    (rowEntry : Interned (EdgeKey Symbol Guard)) :
    let row : EdgeValue Symbol Guard := .mk rowEntry [.empty, .empty]
    let value : Value Symbol Guard := .node entry [row, row] 0 []
    node value = 5 ∧ node value ≤ 1 + 2 * EdgeCount 2 2 1 := by
  intro row value
  have profile : NodeShape 2 2 value := by
    simp [value, row, NodeShape, RowsShape, EdgeShape, ChildrenShape]
  have bounded : height value ≤ 1 := by
    simp [value, row, height, edgesHeight, edgeHeight, childrenHeight]
  exact ⟨rfl, profile_node value profile 1 bounded⟩

theorem ordered_prefixes (first last : List (Value Symbol Guard)) (rows arity countFirst countLast bound : Nat)
    (firstProfile : ChildrenShape rows arity first) (lastProfile : ChildrenShape rows arity last)
    (firstLength : first.length ≤ countFirst) (lastLength : last.length ≤ countLast)
    (firstHeight : childrenHeight first ≤ bound) (lastHeight : childrenHeight last ≤ bound) :
    children (first ++ last) ≤ (countFirst + countLast) * (1 + arity * EdgeCount rows arity bound) ∧
      children (first ++ last) = children first + children last := by
  have firstBound := profile_forest first firstProfile countFirst bound firstLength firstHeight
  have lastBound := profile_forest last lastProfile countLast bound lastLength lastHeight
  exact ⟨by simpa only [children_append, Nat.add_mul] using Nat.add_le_add firstBound lastBound,
    children_append first last⟩

theorem selected_child (entry : Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (row : EdgeValue Symbol Guard) (child : Value Symbol Guard) (rows arity bound : Nat)
    (profile : NodeShape rows arity (.node entry edges depth free))
    (heightBound : height (.node entry edges depth free) ≤ bound)
    (present : row ∈ edges) (member : child ∈ row.children) :
    node child ≤ arity * EdgeCount rows arity bound := by
  have childBound : node child ≤ edge row := by
    cases row with
    | mk rowEntry values => exact child_member values child member
  have literalBound := rows_edges edges profile.2
  have profileBound := (SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.node _ profile bound heightBound).2
  calc
    node child ≤ edge row := childBound
    _ ≤ SourceCurrentAllocatedFiniteOrdinaryValuePositions.rows edges := edge_member edges row present
    _ ≤ arity * (SourceCurrentAllocatedFiniteOrdinaryOccurrences.rows edges).2 := literalBound
    _ ≤ arity * EdgeCount rows arity bound := Nat.mul_le_mul_left _ profileBound

#check @empty_forest
#print axioms empty_forest
#check @repeated_row
#print axioms repeated_row
#check @ordered_prefixes
#print axioms ordered_prefixes
#check @selected_child
#print axioms selected_child

end MicroCFTA.ValuePositionsKernels
