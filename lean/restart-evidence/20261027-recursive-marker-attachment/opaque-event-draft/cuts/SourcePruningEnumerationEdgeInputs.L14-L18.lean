/-- The actual selected-edge children retain inherited and fresh own-class descents. -/
def children (edge : EdgeValue Symbol Constraint) (scs : List Suspended)
    (start : Nat) (tries : List EqualityTrie.Trie) : List (Node × List Suspended) :=
  edge.children.zipIdx.map fun indexed =>
    (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars start tries))
