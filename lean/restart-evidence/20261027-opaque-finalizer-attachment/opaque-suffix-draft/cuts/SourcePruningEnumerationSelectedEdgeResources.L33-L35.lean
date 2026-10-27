    (start : Nat) (tries : List EqualityTrie.Trie) : Nat :=
  SourcePruningEnumerationTraversalCompletion.cost
    (SourcePruningEnumerationEdgeInputs.children edge scs start tries)
