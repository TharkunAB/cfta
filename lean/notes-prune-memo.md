# Nested specialization memo correctness

`MicroCFTA/PruneMemo.lean` models the complete nested memo schedule used by
`specializeNode`, `specializeEdge`, and `specializeChildren`. Each query first
checks its `(state, plan)` key. A miss traverses edges and planned children in
source order, forms the child products, groups candidates, and stores the
completed variants. Unobserved children remain shared graph references.

`specializeMemo_correct` proves exact equality with uncached specialization.
This includes the variant list order and the graph representation, rather
than just accepted-term membership. It derives validity of every nested
cache insertion. The key omits recursion fuel. `specialize_stable` proves
that every sufficient structural budget produces the same exact variants.
The executable budget and plan equality functions have kernel proofs.

`specializeMemo_exact` gives full term coverage and exact sparse observations
for every returned variant. `specializeMemo_extends`, `specializeMemo_hit`,
and `specializeMemo_stored` prove that later calls preserve earlier entries
and that a repeated query returns immediately without child traversal.
These retention proofs do not assume a semantically valid input memo.

`pruneMemo` connects the nested cache to the actual candidate decision loop.
`pruneMemo_exact` proves that each successful result preserves the declared
root-guard language, leaves a valid memo, and retains every earlier memo
entry. It includes ambiguous Unknown fallback and requires sound decided
queries, but does not require every query to be decidable.

The graph interpretation is fixed in these theorems. The source binder table
can grow during recursive pruning. Its adapter must establish that a stored
query has the same graph rows after that growth. In particular, a previously
missing recursive reference must not become a new source of alternatives for
a cached query. Immutable node identities and already resolved references
can establish this condition; memo reuse alone does not establish it.

This model uses the observation and guard fragment of `ObservationGraph`.
The complete source substitution-sensitive observation map, node identity
allocation, mutable Map implementation, and solver behavior remain separate
adapter obligations. The structural fuel bounds finite observation recursion.
It does not prove termination of the outer recursive pruning fixed point.

Validation: `lake build MicroCFTA.PruneMemo` succeeds with the pinned Lean
toolchain. No proof placeholders or new axioms are present.
