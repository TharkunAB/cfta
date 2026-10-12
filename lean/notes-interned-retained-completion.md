# First completion from retained enclosing references

`InternedNestedRootReferences.buildEdges_reference` follows the actual edge
execution and finds every declared unary variable edge in its complete
returned payloads. `build_node_reference` proves that a recursive reference
in such an edge occurs in the actual node's cached free names. The proof
covers empty-child removal, canonical edge order, identity deduplication,
and node-cache hits. Other edges can execute arbitrary nested syntax.
`build_node_filter` proves that source root self filtering leaves the
result of an ordinary node body unchanged.

`InternedRetainedConstruction.Retentive depth expression` checks source
declarations before any key exists. Each binder body must be an ordinary
node. For every enclosing lexical slot, its root must contain a dedicated
unary edge that reads that slot. All children satisfy the same condition
at their actual lexical depth. Symbols and guards need no uniqueness.

Each pending `Frame` stores its original depth and ordinary probes. Its
fresh local name is absent from its depth probe. The completion proof
derives that absence from the actual missing key, fresh reservation, and
the earlier probe's issued-reference provenance. The source syntax places
that fresh name in each inner depth probe. Equal canonical probe identities
would imply equal resident records and equal free-name metadata. The absent
and present name therefore excludes the pending ancestor's key.

`InternedRetainedCompletion.build_completes` composes this argument through
the full nested source schedule. It includes both probes, nested callbacks,
cache hits, actual fresh reservation, and record completion. The proof
derives reference availability, issued-history growth, canonical residency,
and pending-key coverage from the existing source executor invariants.
It does not assume probe separation or a successful first execution.

`closed_completes` and `closed_not_pending` start with empty caches.
`closed_complete_record` supplies complete payload coverage, coherent cached
provenance, edge residency, an available result, and exact later replay.
`tower_complete layers` proves the result for every finite nesting depth.
Every level uses symbol zero. `tower_scoped` checks all lexical variables.

This fragment permits arbitrary nesting of retained fresh dependencies.
It requires dedicated unary root edges for every enclosing slot. It does
not cover a dependency retained only through another nested Mu, or a source
dependency later erased by normalization. The independent and erased-body
completion modules cover separate such cases. General closed-input
completion without these source conditions remains open. The model starts
with prepared guards and does not include public edge-guard validation.
