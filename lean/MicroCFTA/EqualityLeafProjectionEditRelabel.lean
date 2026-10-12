import MicroCFTA.EqualityLeafProjectionEditAgreement

/-!
# Exact target relabeling in source edit requests

Relabeling target payloads preserves path order and first-root selection.
The resulting source request is equal before execution.
-/
namespace MicroCFTA.EqualityLeafProjectionEditRelabel
open InternedConstructorTemplates EqualityLeafProjectionWorkers
open EqualityLeafProjectionSyntax (Path atRoot descendEdits)

/-- Change only each target payload, retaining its complete selected path. -/
def targets (f : Target → Other) (edits : List (Path × Target)) : List (Path × Other) :=
  edits.map fun (path, target) => (path, f target)

/-- First-root lookup commutes with target relabeling. -/
theorem root_targets (f : Target → Other) (edits : List (Path × Target)) :
    atRoot (targets f edits) = (atRoot edits).map f := by
  simp only [atRoot, targets, List.find?_map, Option.map_map]
  rfl

/-- Original path suffixes commute with target relabeling. -/
theorem descend_targets (f : Target → Other) (edits : List (Path × Target)) (index : Nat) :
    descendEdits (targets f edits) index = targets f (descendEdits edits index) := by
  induction edits with
  | nil => rfl
  | cons edit rest ih =>
      obtain ⟨path, target⟩ := edit
      cases path with
      | nil => simpa only [targets, List.map_cons, descendEdits, List.filterMap_cons] using ih
      | cons head path =>
          by_cases same : head = index <;>
            simp [targets, descendEdits, same] at ih ⊢ <;> exact ih

mutual
/-- Relabeled edit payloads execute exactly the corresponding target closures. -/
theorem edit_targets
    (meet : Other → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) (f : Target → Other)
    (edits : List (Path × Target)) (value : Value Symbol Guard) :
    edit meet (targets f edits) value = edit (fun target => meet (f target)) edits value := by
  cases edits with
  | nil => rw [show targets f [] = [] from rfl, edit_unselected, edit_unselected]
  | cons first rest =>
      cases value with
      | empty => rw [edit_empty, edit_empty]
      | reference | union | mu => rfl
      | node entry edges depth free =>
          rw [show targets f (first :: rest) = (first.1, f first.2) :: targets f rest from rfl, edit, edit]
          have root := root_targets f (first :: rest)
          change atRoot ((first.1, f first.2) :: targets f rest) = (atRoot (first :: rest)).map f at root
          rw [root]
          cases selected : atRoot (first :: rest) with
          | some target => rfl
          | none =>
              simp only [Option.map_none]
              rw [← show targets f (first :: rest) = (first.1, f first.2) :: targets f rest from rfl,
                edges_targets meet f (first :: rest) edges]
termination_by sizeOf value

/-- Relabeling preserves every source edge constructor request. -/
theorem edges_targets
    (meet : Other → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) (f : Target → Other)
    (edits : List (Path × Target)) (edges : List (EdgeValue Symbol Guard)) :
    editEdges meet (targets f edits) edges = editEdges (fun target => meet (f target)) edits edges := by
  cases edges with
  | nil => rfl
  | cons edge rest =>
      cases edge with
      | mk entry children =>
          rw [editEdges, editEdges, children_targets meet f edits 0 children]
          congr 1
          funext nodes
          congr 1
          funext edge
          rw [edges_targets meet f edits rest]
termination_by sizeOf edges

/-- Relabeling retains every original child position. -/
theorem children_targets
    (meet : Other → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) (f : Target → Other)
    (edits : List (Path × Target)) (index : Nat) (children : List (Value Symbol Guard)) :
    editChildren meet (targets f edits) index children = editChildren (fun target => meet (f target)) edits index children := by
  cases children with
  | nil => rfl
  | cons child rest =>
      rw [editChildren, editChildren, descend_targets, edit_targets meet f _ child]
      congr 1
      funext node
      rw [children_targets meet f edits (index + 1) rest]
termination_by sizeOf children
end

end MicroCFTA.EqualityLeafProjectionEditRelabel
