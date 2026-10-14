import MicroCFTA.InternedStoredSubstitution

/-!
# Complete shapes of stored substitution leaves

Every captured source leaf is closed or is one literal reference.
Open nodes, unions, and Mu records are traversed instead of captured.
-/
namespace MicroCFTA.InternedStoredLeafShape
open InternedConstructorTemplates InternedStoredSubstitution

mutual
/-- Each actual stored-plan leaf is a closed capture or one reference. -/
theorem leaves_shape (value leaf : Value Symbol Guard) (member : leaf ∈ leaves value) :
    leaf.free = [] ∨ ∃ name, leaf = .reference name := by
  rw [leaves.eq_def] at member
  split at member
  · rename_i closed
    have same := List.mem_singleton.mp member
    exact Or.inl (same ▸ List.isEmpty_iff.mp closed)
  · cases value with
    | empty =>
        have same := List.mem_singleton.mp member
        exact Or.inl (same ▸ rfl)
    | reference name => exact Or.inr ⟨name, List.mem_singleton.mp member⟩
    | node entry edges depth free => exact edgeLeaves_shape edges leaf member
    | union entry members depth free => exact manyLeaves_shape members leaf member
    | mu entry body depth ordinary => exact leaves_shape body leaf member
termination_by sizeOf value

/-- Leaves from ordered operands have the same closed-or-reference shape. -/
theorem manyLeaves_shape (values : List (Value Symbol Guard)) (leaf : Value Symbol Guard)
    (member : leaf ∈ manyLeaves values) : leaf.free = [] ∨ ∃ name, leaf = .reference name := by
  cases values with
  | nil => simp [manyLeaves] at member
  | cons first rest =>
      rw [manyLeaves, List.mem_append] at member
      rcases member with head | tail
      · exact leaves_shape first leaf head
      · exact manyLeaves_shape rest leaf tail
termination_by sizeOf values

/-- Leaves from ordered edge children have the same closed-or-reference shape. -/
theorem edgeLeaves_shape (edges : List (EdgeValue Symbol Guard)) (leaf : Value Symbol Guard)
    (member : leaf ∈ edgeLeaves edges) : leaf.free = [] ∨ ∃ name, leaf = .reference name := by
  cases edges with
  | nil => simp [edgeLeaves] at member
  | cons first rest =>
      cases first with
      | mk entry values =>
          rw [edgeLeaves, List.mem_append] at member
          rcases member with head | tail
          · exact manyLeaves_shape values leaf head
          · exact edgeLeaves_shape rest leaf tail
termination_by sizeOf edges
end

end MicroCFTA.InternedStoredLeafShape
