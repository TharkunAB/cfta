import MicroCFTA.EqualityTriePathFamily

namespace MicroCFTA.EqualityTrie.CollectionFamily

open MicroCFTA.EqualityTrie

-- Choose or drop each original position. Keep duplicates.
def family {Variable : Type} :
    List (Suspended Variable) → List (List (Suspended Variable))
  | [] => [[]]
  | constraint :: rest =>
      family rest ++
        (PathFamily.family constraint.trie).flatMap (fun trie =>
          (family rest).map (fun tail => Suspended.mk trie constraint.var :: tail))

private theorem original_mem_family {Variable : Type}
    (original : List (Suspended Variable)) : original ∈ family original := by
  induction original with
  | nil =>
      exact List.mem_cons.mpr (Or.inl rfl)
  | cons constraint rest previous =>
      have trieMember := (PathFamily.family_joint constraint.trie).1
      have headMember : constraint :: rest ∈
          (family rest).map (fun tail => Suspended.mk constraint.trie constraint.var :: tail) :=
        List.mem_map.mpr ⟨rest, previous, by cases constraint <;> rfl⟩
      exact List.mem_append.mpr
        (Or.inr (List.mem_flatMap.mpr ⟨constraint.trie, trieMember, headMember⟩))

private theorem descend_nil {Variable : Type} (index : Nat) :
    descendScs (Variable := Variable) index [] = [] := by
  simp only [descendScs, List.map_nil, List.filter_nil]

private theorem descend_cons_cases {Variable : Type} (index : Nat)
    (head : Suspended Variable) (tail : List (Suspended Variable)) :
    descendScs index (head :: tail) = descendScs index tail ∨
    descendScs index (head :: tail) =
      Suspended.mk (pathTrieDescend head.trie index) head.var :: descendScs index tail := by
  simp only [descendScs, List.map_cons, List.filter_cons]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

private theorem family_closed {Variable : Type} (original : List (Suspended Variable)) :
    ∀ pending ∈ family original, ∀ index,
      descendScs index pending ∈ family original := by
  induction original with
  | nil =>
      intro pending member index
      rcases List.mem_cons.mp member with same | impossible
      · subst pending
        rw [descend_nil]
        exact List.mem_cons.mpr (Or.inl rfl)
      · cases impossible
  | cons constraint rest previous =>
      intro pending member index
      rcases List.mem_append.mp member with dropped | selected
      · have result := previous pending dropped index
        exact List.mem_append.mpr (Or.inl result)
      · rcases List.mem_flatMap.mp selected with ⟨trie, trieMember, tailsMember⟩
        rcases List.mem_map.mp tailsMember with ⟨tail, tailMember, same⟩
        subst pending
        have tailResult := previous tail tailMember index
        rcases descend_cons_cases index (Suspended.mk trie constraint.var) tail with
          erased | retained
        · rw [erased]
          exact List.mem_append.mpr (Or.inl tailResult)
        · rw [retained]
          have trieResult :=
            (PathFamily.family_joint constraint.trie).2.2.1 trie trieMember index
          have chosenOutput :
              Suspended.mk (pathTrieDescend trie index) constraint.var ::
                descendScs index tail ∈
              (family rest).map (fun remaining =>
                Suspended.mk (pathTrieDescend trie index) constraint.var :: remaining) :=
            List.mem_map.mpr ⟨descendScs index tail, tailResult, rfl⟩
          exact List.mem_append.mpr
            (Or.inr (List.mem_flatMap.mpr
              ⟨pathTrieDescend trie index, trieResult, chosenOutput⟩))

-- Use the length of the same computed family as the index budget.
theorem family_joint {Variable : Type} (original : List (Suspended Variable)) :
    original ∈ family original ∧
    (∀ pending ∈ family original, ∀ index,
      descendScs index pending ∈ family original) ∧
    (∀ pending, pending ∈ family original ↔
      ∃ index, ∃ (within : index < (family original).length),
        (family original)[index] = pending) := by
  exact ⟨original_mem_family original, family_closed original,
    fun _ => List.mem_iff_getElem⟩

end MicroCFTA.EqualityTrie.CollectionFamily
