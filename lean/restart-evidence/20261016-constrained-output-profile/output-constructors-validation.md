# Actual output constructor profile validation

Validated: 2026-10-16 19:19 CEST.
Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.lean` (122 lines).
SHA-256: `08a7b6902d8b428c04fda6ac1057104ffbdd47b461e94c72a1db7c40803ca02f`.

`makeEdge` derives the actual returned EdgeShape from the literal ChildrenShape, child count, initial Coherent/Cached, and availability of those children. Exact complete-child readback covers cache hits. `makeNode` derives the actual returned NodeShape from the literal RowsShape, row count, initial Coherent/Linked, and residency of those rows. Exact ordinary-node readback covers cache hits. The empty normalized case returns Empty. Guards and cached metadata have no added profile restriction.

The helpers construct ordered list profiles from membership or All₂ facts. Subset, filter, and canonical selection retain every complete selected row profile. Canonical edge identity deduplication and sorting cannot increase length. Empty-child filtering cannot increase length. All₂ collection retains exact positional list length.

Validation passed:
- Direct source: `output-constructors-direct-1.log`, exit 0, no warnings.
- Root canonical build: `output-constructors-build-1.log`, exit 0, 395 jobs.
- Eleven public axiom/full-signature pairs: `output-constructors-public-1.log`, exit 0.
- Four integration axiom/signature pairs: `output-constructors-kernels-4.log`, exit 0, no warnings or `sorryAx`.

The kernels build an actual nullary resident edge and a duplicate-row node, show the canonical row count is one, and replay the node at the exact returned whole heap. A second kernel constructs a literal sentinel, proves its arity-one profile and failure of an arity-zero profile, then proves node filtering erases it. The generic warm kernel derives the same output profile on actual replay. The positional child kernel composes All₂ profiles and exact lengths with literal edge construction.

The module proves local constructor/profile laws. It does not derive recursive native output profiles, cache producer invariants, query reservation totals, cumulative Target resources, termination, or host runtime correspondence. Parent producer proofs must derive the input list profiles from actual smaller calls. No prior proof, Haskell source, Audit, documentation, or prior evidence was edited. No Lake process ran here. Earlier failed kernel logs remain diagnostic evidence.
