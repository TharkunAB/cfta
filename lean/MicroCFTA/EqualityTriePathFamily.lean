import MicroCFTA.EqualityTrie

namespace MicroCFTA.EqualityTrie.PathFamily

open MicroCFTA.EqualityTrie

-- List every stored child trie. Keep duplicates.
mutual
  def family : Trie → List Trie
    | .empty => [.empty]
    | .terminal => [.empty, .terminal]
    | .branch children => [.empty, .branch children] ++ childFamilies children

  private def childFamilies : List (Nat × Trie) → List Trie
    | [] => []
    | (_, child) :: rest => family child ++ childFamilies rest
end

private theorem childFamilies_eq_flatMap (children : List (Nat × Trie)) :
    childFamilies children = children.flatMap (fun entry => family entry.2) := by
  induction children with
  | nil =>
      rfl
  | cons entry rest previous =>
      rcases entry with ⟨key, child⟩
      change family child ++ childFamilies rest =
        family child ++ rest.flatMap (fun item => family item.2)
      rw [previous]

private theorem family_branch (children : List (Nat × Trie)) :
    family (.branch children) =
      [.empty, .branch children] ++ children.flatMap (fun entry => family entry.2) := by
  change [.empty, .branch children] ++ childFamilies children =
    [.empty, .branch children] ++ children.flatMap (fun entry => family entry.2)
  rw [childFamilies_eq_flatMap]

private theorem original_mem_family (original : Trie) : original ∈ family original := by
  cases original with
  | empty =>
      exact List.mem_cons.mpr (Or.inl rfl)
  | terminal =>
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  | branch children =>
      rw [family_branch]
      exact List.mem_append.mpr
        (Or.inl (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem empty_mem_family (original : Trie) : Trie.empty ∈ family original := by
  cases original with
  | empty =>
      exact List.mem_cons.mpr (Or.inl rfl)
  | terminal =>
      exact List.mem_cons.mpr (Or.inl rfl)
  | branch children =>
      rw [family_branch]
      exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inl rfl)))

mutual
  private theorem family_closed (original : Trie) :
      ∀ current ∈ family original, ∀ index,
        pathTrieDescend current index ∈ family original := by
    cases original with
    | empty =>
        intro current member index
        rcases List.mem_cons.mp member with same | impossible
        · subst current
          exact empty_mem_family .empty
        · cases impossible
    | terminal =>
        intro current member index
        rcases List.mem_cons.mp member with same | remaining
        · subst current
          exact empty_mem_family .terminal
        · rcases List.mem_cons.mp remaining with same | impossible
          · subst current
            exact empty_mem_family .terminal
          · cases impossible
    | branch children =>
        intro current member index
        rw [family_branch] at member
        rcases List.mem_append.mp member with frontMembers | nested
        · rcases List.mem_cons.mp frontMembers with same | remaining
          · subst current
            exact empty_mem_family (.branch children)
          · rcases List.mem_cons.mp remaining with same | impossible
            · subst current
              cases found : lookup index children with
              | none =>
                  have reduced : (none : Option Trie).getD Trie.empty = Trie.empty := by rfl
                  simpa only [pathTrieDescend, found, reduced] using
                    empty_mem_family (.branch children)
              | some child =>
                  have selected : (index, child) ∈ children :=
                    lookup_mem index children child found
                  have nestedMember : child ∈ children.flatMap (fun entry => family entry.2) :=
                    List.mem_flatMap.mpr ⟨(index, child), selected, original_mem_family child⟩
                  have result : child ∈ family (.branch children) := by
                    rw [family_branch]
                    exact List.mem_append.mpr (Or.inr nestedMember)
                  have reduced : (some child).getD Trie.empty = child := by rfl
                  simpa only [pathTrieDescend, found, reduced] using result
            · cases impossible
        · have result := children_closed children current nested index
          rw [family_branch]
          exact List.mem_append.mpr (Or.inr result)

  private theorem children_closed (children : List (Nat × Trie)) :
      ∀ current ∈ children.flatMap (fun entry => family entry.2), ∀ index,
        pathTrieDescend current index ∈ children.flatMap (fun entry => family entry.2) := by
    cases children with
    | nil =>
        intro current member index
        rcases List.mem_flatMap.mp member with ⟨entry, impossible, _⟩
        cases impossible
    | cons entry rest =>
        rcases entry with ⟨key, child⟩
        intro current member index
        rcases List.mem_flatMap.mp member with ⟨selected, selectedMember, nestedMember⟩
        rcases List.mem_cons.mp selectedMember with same | inRest
        · subst selected
          have result := family_closed child current nestedMember index
          exact List.mem_flatMap.mpr
            ⟨(key, child), List.mem_cons.mpr (Or.inl rfl), result⟩
        · have restMember : current ∈ rest.flatMap (fun item => family item.2) :=
            List.mem_flatMap.mpr ⟨selected, inRest, nestedMember⟩
          have restResult := children_closed rest current restMember index
          rcases List.mem_flatMap.mp restResult with ⟨selectedAgain, selectedAgainMember, result⟩
          exact List.mem_flatMap.mpr
            ⟨selectedAgain, List.mem_cons.mpr (Or.inr selectedAgainMember), result⟩
end

-- The budget is the length of the computed list.
theorem family_joint (original : Trie) :
    original ∈ family original ∧
    Trie.empty ∈ family original ∧
    (∀ current ∈ family original, ∀ index,
      pathTrieDescend current index ∈ family original) ∧
    (∀ current, current ∈ family original ↔
      ∃ index, ∃ (within : index < (family original).length),
        (family original)[index] = current) := by
  exact ⟨original_mem_family original, empty_mem_family original, family_closed original,
    fun _ => List.mem_iff_getElem⟩

end MicroCFTA.EqualityTrie.PathFamily
