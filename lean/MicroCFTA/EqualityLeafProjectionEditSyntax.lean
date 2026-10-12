import MicroCFTA.EqualityLeafProjectionLowering

/-!
# Empty simultaneous edit lists

An empty edit list changes no occurrence or original child position.
-/
namespace MicroCFTA.EqualityLeafProjectionEditSyntax
open EqualityLeafProjectionSyntax

mutual
/-- No selected paths leave an occurrence unchanged. -/
theorem edit_nil (join : Leaf → Leaf → Leaf) (tree : Tree Tag Leaf) : edit join [] tree = tree := by
  cases tree with
  | empty => rfl
  | leaf value => rfl
  | node edges => simp only [edit, edges_nil join edges]

/-- No selected paths leave the original row list unchanged. -/
theorem edges_nil (join : Leaf → Leaf → Leaf) (edges : List (Edge Tag Leaf)) : editEdges join [] edges = edges := by
  cases edges with
  | nil => rfl
  | cons edge rest =>
      cases edge with
      | mk tag children => simp only [editEdges, children_nil join 0 children, edges_nil join rest]

/-- No selected paths leave the ordered child forest unchanged. -/
theorem children_nil (join : Leaf → Leaf → Leaf) (index : Nat) (children : List (Tree Tag Leaf)) :
    editChildren join [] index children = children := by
  cases children with
  | nil => rfl
  | cons child rest =>
      simp only [editChildren, descendEdits, List.filterMap_nil, edit_nil join child, children_nil join (index + 1) rest]
end

end MicroCFTA.EqualityLeafProjectionEditSyntax
