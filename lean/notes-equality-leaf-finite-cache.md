# Finite-cache occurrence lowering

`EqualityLeafProjectionCompile` compiles an original occurrence forest with
actual ordered child, edge, and node requests. Leaf construction remains a
parameter so the canonical and raw admission carriers can use the same
ancestor compiler. Literal ancestor fields derive constructor safety.

`compile_lower`, `compileEdges_lower`, and `compileForest_lower` prove exact
readback in any common cache that retains the completed finite computation.
The proofs follow the actual bind states and derive replay of each component.
`completed_forest` constructs that cache by executing the finite forest. It
also derives coherence, growth, exact lowering, and allocation-free replay.
`same_forest` gives equality of complete physical records from equal original
forests whose completed requests reside in the same cache.

The snapshot contains the actual finite edit and require workers. These
constructor results do not assert universal `ConstructorLaws` for a fixed
finite cache. Such a cache cannot contain all possible constructor requests.
The remaining correspondence must use the finite requests of each actual
pass and its retained occurrence representation.

`EqualityLeafProjectionLeafWorkers` derives the nullary base case for the
actual required-path worker. Every constructed outgoing row has no children.
A proper child requirement therefore deletes all rows before child recursion.
Root-only requirements return the exact original record. `built_require`
proves the complete `Work` equation, including absence of allocation, from
the actual nullary builder. It has no supplied worker-correctness premise.
