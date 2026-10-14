import MicroCFTA.InternedStoredSubstitution
import MicroCFTA.InternedNormalizationFree

/-!
# Ordinary names in actual stored substitution leaves

An ordinary name in a source leaf also occurs in the original stored body.
Coherent cached metadata supplies node and union free-name fields.
An interned Mu binder cannot remove an ordinary name.
-/
namespace MicroCFTA.InternedStoredLeavesOrdinary
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution
open InternedNestedProvenance (Values)
open InternedBinderProtocol (Reference)

mutual
/-- Every ordinary name in an actual available leaf is free in the original stored value. -/
theorem leaves_ordinary (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state value) (leaf : Value Symbol Guard) (member : leaf ∈ leaves value)
    (level : Nat) (free : .uninterned level ∈ leaf.free) : .uninterned level ∈ value.free := by
  rw [leaves.eq_def] at member
  split at member
  · have same := List.mem_singleton.mp member
    exact same ▸ free
  · cases value with
    | empty | reference =>
        have same := List.mem_singleton.mp member
        exact same ▸ free
    | node entry edges depth cached =>
        obtain ⟨child, included, captured⟩ := edgeLeaves_ordinary edges state coherent
          (fun child inside => available.children child inside) leaf member level free
        rw [Value.free, InternedNormalizationFree.node_free state coherent entry edges depth cached available.resident,
          childFree_member]
        exact ⟨child, included, captured⟩
    | union entry members depth cached =>
        obtain ⟨child, included, captured⟩ := manyLeaves_ordinary members state coherent
          (fun child inside => available.children child inside) leaf member level free
        rw [Value.free, InternedNormalizationFree.union_free state coherent entry members depth cached available.resident,
          childFree_member]
        exact ⟨child, included, captured⟩
    | mu entry body depth ordinary =>
        have captured := leaves_ordinary body state coherent
          (available.children body (by simp [children])) leaf member level free
        simp only [Value.free, List.mem_filter, bne_iff_ne]
        exact ⟨captured, by intro impossible; cases impossible⟩
termination_by sizeOf value

/-- An ordinary name in an ordered leaf list comes from one actual original child. -/
theorem manyLeaves_ordinary (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state values) (leaf : Value Symbol Guard) (member : leaf ∈ manyLeaves values)
    (level : Nat) (free : .uninterned level ∈ leaf.free) :
    ∃ value ∈ values, .uninterned level ∈ value.free := by
  cases values with
  | nil => simp [manyLeaves] at member
  | cons first rest =>
      rw [manyLeaves] at member
      rcases List.mem_append.mp member with head | tail
      · exact ⟨first, List.mem_cons_self,
          leaves_ordinary first state coherent (available first List.mem_cons_self) leaf head level free⟩
      · obtain ⟨value, included, captured⟩ := manyLeaves_ordinary rest state coherent
          (fun value inside => available value (List.mem_cons_of_mem first inside)) leaf tail level free
        exact ⟨value, List.mem_cons_of_mem first included, captured⟩
termination_by sizeOf values

/-- An ordinary name in edge leaves comes from an actual ordered edge child. -/
theorem edgeLeaves_ordinary (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state (edges.flatMap EdgeValue.children))
    (leaf : Value Symbol Guard) (member : leaf ∈ edgeLeaves edges)
    (level : Nat) (free : .uninterned level ∈ leaf.free) :
    ∃ value ∈ edges.flatMap EdgeValue.children, .uninterned level ∈ value.free := by
  cases edges with
  | nil => simp [edgeLeaves] at member
  | cons first rest =>
      cases first with
      | mk entry values =>
          rw [edgeLeaves] at member
          rcases List.mem_append.mp member with head | tail
          · obtain ⟨value, included, captured⟩ := manyLeaves_ordinary values state coherent
              (fun value inside => available value (by simp [EdgeValue.children, inside])) leaf head level free
            exact ⟨value, by simp [EdgeValue.children, included], captured⟩
          · obtain ⟨value, included, captured⟩ := edgeLeaves_ordinary rest state coherent
              (fun value inside => available value (by simp [EdgeValue.children, inside])) leaf tail level free
            exact ⟨value, by simp [EdgeValue.children, included], captured⟩
termination_by sizeOf edges
end

end MicroCFTA.InternedStoredLeavesOrdinary
