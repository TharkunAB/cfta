import MicroCFTA.MergedSourceGrouping

/-!
# Per-key row bounds from actual source grouping

The executable partition removes each complete key class before it
recurses. Thus at most one output group can contribute a queried key.
-/
namespace MicroCFTA.MergedGroupPartitionBound
open Language
variable {Item Key : Type}

/-- One completed group keeps its source key and satisfies a row bound. -/
def GroupPost (key : Item → Key) (limit : Nat) (inputs outputs : List Item) : Prop :=
  outputs.length ≤ limit ∧ ∀ output ∈ outputs, ∀ input ∈ inputs, key output = key input

/-- Two actual source groups that contain the same key are the same complete class. -/
theorem same_key_group [DecidableEq Key] (key : Item → Key) (inputs : List Item)
    (first second : List Item) (firstIn : first ∈ Sized.groups key inputs) (secondIn : second ∈ Sized.groups key inputs)
    (left right : Item) (leftIn : left ∈ first) (rightIn : right ∈ second) (same : key left = key right) : first = second := by
  obtain ⟨a, rest, shape, exactFirst⟩ := MergedSourceGrouping.groups_exact key inputs first firstIn
  obtain ⟨b, tail, otherShape, exactSecond⟩ := MergedSourceGrouping.groups_exact key inputs second secondIn
  have firstMember : left ∈ inputs.filter (fun item => decide (key item = key a)) := exactFirst ▸ leftIn
  have firstKey : key left = key a := by simpa only [decide_eq_true_eq] using (List.mem_filter.mp firstMember).2
  have secondMember : right ∈ inputs.filter (fun item => decide (key item = key b)) := exactSecond ▸ rightIn
  have secondKey : key right = key b := by simpa only [decide_eq_true_eq] using (List.mem_filter.mp secondMember).2
  have equal : key a = key b := firstKey.symm.trans (same.trans secondKey)
  rw [exactFirst, exactSecond, equal]

/-- Each returned item has a source item in its originating nonempty group. -/
theorem output_origin (key : Item → Key) (limit : Nat) (inputs outputs : List (List Item))
    (nonempty : ∀ group ∈ inputs, ∃ item ∈ group, True)
    (related : All₂ (GroupPost key limit) inputs outputs) (output : Item) (member : output ∈ outputs.flatten) :
    ∃ input ∈ inputs.flatten, key output = key input := by
  induction related with
  | nil => simp at member
  | @cons source result sources results first rest ih =>
      rcases List.mem_append.mp member with before | later
      · obtain ⟨input, included, _⟩ := nonempty source List.mem_cons_self
        exact ⟨input, List.mem_append.mpr (Or.inl included), first.2 output before input included⟩
      · obtain ⟨input, included, same⟩ := ih
          (fun group present => nonempty group (List.mem_cons_of_mem _ present)) later
        exact ⟨input, List.mem_append.mpr (Or.inr included), same⟩

/-- Actual source partitioning derives every returned key's original occurrence. -/
theorem source_output_origin [DecidableEq Key] (key : Item → Key) (limit : Nat)
    (inputs : List Item) (outputs : List (List Item))
    (related : All₂ (GroupPost key limit) (Sized.groups key inputs) outputs)
    (output : Item) (member : output ∈ outputs.flatten) : ∃ input ∈ inputs, key output = key input := by
  have nonempty : ∀ group ∈ Sized.groups key inputs, ∃ item ∈ group, True := by
    intro group included
    obtain ⟨first, rest, same, _⟩ := Sized.groups_constant key inputs group included
    exact ⟨first, by simp [same], trivial⟩
  obtain ⟨input, included, same⟩ := output_origin key limit (Sized.groups key inputs) outputs nonempty related output member
  exact ⟨input, (Sized.groups_perm key inputs).mem_iff.mp included, same⟩

/-- A query receives rows from at most one actual source group. -/
theorem filter_bound [DecidableEq Key] (key : Item → Key) (limit : Nat)
    (inputs : List Item) (outputs : List (List Item))
    (related : All₂ (GroupPost key limit) (Sized.groups key inputs) outputs) (query : Key) :
    (outputs.flatten.filter (fun item => decide (key item = query))).length ≤ limit := by
  induction inputs using Sized.groups.induct key generalizing outputs with
  | case1 =>
      simp only [Sized.groups] at related
      cases related
      simp
  | case2 first rest ih =>
      rw [List.unattach_filter (g := fun other => decide (key other ≠ key first))
        (hf := fun _ _ => rfl), List.unattach_attach] at ih
      rw [Sized.groups] at related
      cases related with
      | @cons source group sources restGroups firstPost restPost =>
          by_cases same : key first = query
          · have noLater : restGroups.flatten.filter (fun item => decide (key item = query)) = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro item included
              obtain ⟨source, present, sourceKey⟩ := source_output_origin key limit _ _ restPost item included
              have different : key source ≠ key first := of_decide_eq_true (List.mem_filter.mp present).2
              simp only [decide_eq_true_eq]
              intro equal
              exact different (sourceKey.symm.trans (equal.trans same.symm))
            simpa only [List.flatten_cons, List.filter_append, noLater, List.length_append, List.length_nil, Nat.add_zero]
              using Nat.le_trans (List.length_filter_le (fun item => decide (key item = query)) group) firstPost.1
          · have noFirst : group.filter (fun item => decide (key item = query)) = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro item included
              have sourceKey := firstPost.2 item included first List.mem_cons_self
              simp only [decide_eq_true_eq]
              exact fun equal => same (sourceKey.symm.trans equal)
            simpa only [List.flatten_cons, List.filter_append, noFirst, List.length_append, List.length_nil, Nat.zero_add]
              using ih restGroups restPost

/-- The source four-row threshold holds for each key in the complete returned root. -/
theorem four_rows [DecidableEq Key] (key : Item → Key)
    (inputs : List Item) (outputs : List (List Item))
    (related : All₂ (GroupPost key 4) (Sized.groups key inputs) outputs) (query : Key) :
    (outputs.flatten.filter (fun item => decide (key item = query))).length ≤ 4 :=
  filter_bound key 4 inputs outputs related query

/-- Lawful Boolean key equality has the same complete-root row bound. -/
theorem filter_bound_beq [DecidableEq Key] [BEq Key] [LawfulBEq Key] (key : Item → Key) (limit : Nat)
    (inputs : List Item) (outputs : List (List Item))
    (related : All₂ (GroupPost key limit) (Sized.groups key inputs) outputs) (query : Key) :
    (outputs.flatten.filter (fun item => key item == query)).length ≤ limit := by
  have same : (fun item => key item == query) = (fun item => decide (key item = query)) := by
    funext item
    exact Bool.eq_iff_iff.mpr (by simp)
  rw [same]
  exact filter_bound key limit inputs outputs related query

/-- Reordering source positions can reorder their related outputs by the same permutation. -/
theorem permute_related (relation : A → B → Prop) (first second : List A)
    (permutation : first.Perm second) (outputs : List B) (related : All₂ relation first outputs) :
    ∃ reordered, outputs.Perm reordered ∧ All₂ relation second reordered := by
  induction permutation generalizing outputs with
  | nil => cases related; exact ⟨[], .nil, .nil⟩
  | cons item permutation ih =>
      cases related with
      | cons head tail =>
          obtain ⟨reordered, ordered, matched⟩ := ih _ tail
          exact ⟨_ :: reordered, ordered.cons _, .cons head matched⟩
  | swap first second rest =>
      cases related with
      | cons firstRelated remaining =>
          cases remaining with
          | cons secondRelated tail => exact ⟨_, .swap _ _ _, .cons secondRelated (.cons firstRelated tail)⟩
  | trans first second ihFirst ihSecond =>
      obtain ⟨middle, firstOrder, firstRelated⟩ := ihFirst outputs related
      obtain ⟨final, secondOrder, secondRelated⟩ := ihSecond middle firstRelated
      exact ⟨final, firstOrder.trans secondOrder, secondRelated⟩

/-- Arbitrary source bucket order retains the complete-root per-key row bound. -/
theorem filter_bound_permutation [DecidableEq Key] (key : Item → Key) (limit : Nat)
    (inputs : List Item) (sourceGroups outputs : List (List Item))
    (permutation : sourceGroups.Perm (Sized.groups key inputs))
    (related : All₂ (GroupPost key limit) sourceGroups outputs) (query : Key) :
    (outputs.flatten.filter (fun item => decide (key item = query))).length ≤ limit := by
  obtain ⟨reordered, ordered, matched⟩ := permute_related (GroupPost key limit) sourceGroups
    (Sized.groups key inputs) permutation outputs related
  have same := (ordered.flatten.filter (fun item => decide (key item = query))).length_eq
  rw [same]
  exact filter_bound key limit inputs reordered matched query

end MicroCFTA.MergedGroupPartitionBound
