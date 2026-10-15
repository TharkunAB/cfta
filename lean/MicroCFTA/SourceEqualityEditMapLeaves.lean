import MicroCFTA.SourceEqualityEdits

/-!
# Leaf occurrence readback through one signed map alteration

An ascending map changes one child block. If that block adds one leaf, the
whole flattened map adds precisely that occurrence. The proof keeps all old
leaf occurrences and requires no ordering on callback payloads.
-/
namespace MicroCFTA.SourceEqualityEditMapLeaves
open SourceEqualityNeededMap

/-- One altered child block adds exactly its one new flattened occurrence. -/
theorem alter_flatMap (key : Int) (change : Option α → α) (entries : List (Int × α))
    (ordered : Ascending entries) (flatten : Int → α → List β) (newLeaf : β)
    (changed : (flatten key (change (lookup key entries))).Perm
      (newLeaf :: (lookup key entries).toList.flatMap (flatten key))) :
    ((alter key change entries).flatMap (fun entry => flatten entry.1 entry.2)).Perm
      (newLeaf :: entries.flatMap (fun entry => flatten entry.1 entry.2)) := by
  induction entries with
  | nil => simpa only [lookup, alter, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Option.toList_none] using changed
  | cons entry rest ih =>
      obtain ⟨index, value⟩ := entry
      have order := List.pairwise_cons.mp ordered
      by_cases earlier : key < index
      · have missing : lookup key ((index, value) :: rest) = none := by
          apply lookup_none
          intro other child member
          rcases List.mem_cons.mp member with same | member
          · cases same; omega
          · have larger := order.1 (other, child) member
            dsimp at larger
            omega
        have selected : (flatten key (change none)).Perm [newLeaf] := by
          simpa only [missing, Option.toList_none, List.flatMap_nil] using changed
        rw [alter, ite_eq_left earlier, List.flatMap_cons]
        simpa only [List.singleton_append] using selected.append_right
          (((index, value) :: rest).flatMap (fun entry => flatten entry.1 entry.2))
      · by_cases same : key = index
        · subst index
          have selected : (flatten key (change (some value))).Perm (newLeaf :: flatten key value) := by
            simpa [lookup] using changed
          rw [alter, ite_eq_right (by omega), ite_eq_left rfl, List.flatMap_cons, List.flatMap_cons]
          exact selected.append_right _
        · have selected : (flatten key (change (lookup key rest))).Perm
              (newLeaf :: (lookup key rest).toList.flatMap (flatten key)) := by
            simpa only [lookup, ite_eq_right same] using changed
          rw [alter, ite_eq_right earlier, ite_eq_right same, List.flatMap_cons, List.flatMap_cons]
          exact (List.Perm.append_left (flatten index value) (ih order.2 selected)).trans List.perm_middle

end MicroCFTA.SourceEqualityEditMapLeaves
