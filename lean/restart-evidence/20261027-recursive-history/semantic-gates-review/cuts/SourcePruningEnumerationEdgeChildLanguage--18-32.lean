private theorem retained_holds (incoming : Node) (bucket : List Suspended)
    (assignment : Nat → Term Symbol) (term : Term Symbol)
    (retained : (match incoming with | .node _ _ _ _ => True | _ => False) ∨
      bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = [])
    (effective : ∀ sc ∈ (match incoming with
      | .node _ _ _ _ => bucket
      | _ => if bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) then bucket else []),
      Suspended.Holds assignment term sc) :
    ∀ sc ∈ bucket, Suspended.Holds assignment term sc := by
  cases incoming <;> first
    | exact effective
    | rcases retained with ordinary | hasTerminal | emptyBucket
      · cases ordinary
      · simpa only [hasTerminal, ↓reduceIte] using effective
      · simp only [emptyBucket, List.not_mem_nil, false_implies, implies_true]
