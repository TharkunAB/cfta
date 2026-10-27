def bucket : List Suspended := [⟨.branch [(0, .terminal)], 1⟩]

/-- Trie validity does not provide the structural retention gate for a nonordinary child. -/
theorem valid_bucket_not_retained {NativeGuard : Type}
    (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (nonordinary : match value with | .node _ _ _ _ => False | _ => True) :
    ValidSuspended bucket ∧ bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false ∧
      ¬ ((match value with | .node _ _ _ _ => True | _ => False) ∨
        bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = []) := by
