/-- Install one witness per fresh class while preserving the pre-existing variable prefix. -/
def install (assignment : Nat → Term Symbol) (start : Nat) : List (Term Symbol) → Nat → Term Symbol
  | [] => assignment
  | term :: rest => install (fun uv => if uv = start then term else assignment uv) (start + 1) rest

/-- Fresh class witnesses do not change any previously allocated value. -/
theorem install_before (assignment : Nat → Term Symbol) (start : Nat) (terms : List (Term Symbol))
    (uv : Nat) (earlier : uv < start) : install assignment start terms uv = assignment uv := by
  induction terms generalizing start assignment with
  | nil => rfl
  | cons term rest ih =>
      rw [install, ih _ _ (by omega)]
      simp [show uv ≠ start by omega]

/-- Every finite collection of satisfied equality classes has a same-length witness vector. -/
theorem equality_witnesses (term : Term Symbol) (tries : List EqualityTrie.Trie)
    (holds : ∀ trie ∈ tries, EqualityHolds term trie) :
    ∃ witnesses, All₂ (fun trie common => ∀ path ∈ EqualityTrie.fromPathTrie trie,
      term.atPath path = some common) tries witnesses := by
  induction tries with
  | nil => exact ⟨[], .nil⟩
  | cons trie rest ih =>
      obtain ⟨common, paths⟩ := holds trie (by simp)
      obtain ⟨witnesses, remaining⟩ := ih (fun next member => holds next (by simp [member]))
      exact ⟨common :: witnesses, .cons paths remaining⟩

/-- Installing the witness vector satisfies the exact variables produced by suspension. -/
theorem installed_classes (term : Term Symbol) (tries : List EqualityTrie.Trie) (witnesses : List (Term Symbol))
    (valid : All₂ (fun trie common => ∀ path ∈ EqualityTrie.fromPathTrie trie,
      term.atPath path = some common) tries witnesses)
    (assignment : Nat → Term Symbol) (start : Nat) :
    ∀ sc ∈ suspendedVars start tries, Suspended.Holds (install assignment start witnesses) term sc := by
  induction valid generalizing assignment start with
  | nil => simp [suspendedVars]
  | @cons trie common rest remaining head tail ih =>
      intro sc member
      simp only [suspendedVars, List.mem_cons] at member
      rcases member with same | member
      · subst sc
        intro path present
        simp only [install]
        rw [install_before _ (start + 1) remaining start (by omega)]
        simpa using head path present
      · exact ih _ _ sc member
