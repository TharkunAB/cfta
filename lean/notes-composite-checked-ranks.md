# Composite checked-symbol certificates

`CompositeCheckedRanks` retains the actual flags from finite argument chains,
n-way joins, arbitrary retained frequency choices, enumerated callbacks, and
imported term adapters. It reuses the finite child callback proofs in
`StaticCheckedRanks` and `StaticRankQueryExact`.

The chain callback intentionally ignores argument keys. Its certificate
therefore covers selected payload terms, not complete argument wrappers.
`join_keys_exact` derives the missing wrapper information from the actual
`joinKeysMatch` checks: equal key and argument counts, exact component and
position indices, nullary key leaves, and two-child argument wrappers.
The resulting center and argument lists are precisely those constructed by
`SupportJoin.joinTerm`.

`join_checked` derives successful `selectJoin` replay and exact requested
projection in all three views. Its proof composes the key certificate with
selected operation and argument payloads. `join_certified_complete` retains
every selected tuple when the child label matchers accept their own symbols.
`chain_valid` and `join_valid` prove strict candidate order and cardinality
bounds, including unchecked candidates. Erasure theorems reproduce the
existing `StaticCompositeCandidateRanks` callbacks exactly.

The frequency proofs cover arbitrary finite lists of retained alternatives.
They derive branch indices and cumulative cardinality offsets from source
order. `frequency_checked` proves exact selector replay.
`frequency_certified_complete` retains every selected branch member.
`frequency_valid` proves strict order and bounds, including zero-cardinality
branches. Equal terms from different members retain their distinct ranks.

Enumerated callbacks check complete projected terms. Their certificates,
completeness, strict order, and bounds follow from the actual list scan.
No closed-term or integer-fill assumption is needed for this original-view
result. Those conditions belong to the separate integer-settlement adapter.

The imported adapter traverses every symbol with `userTerm`. It rejects any
private label and preserves the entire tree on success. Its emitted true
flag follows from a backend rank-to-selection certificate. This local backend
contract remains explicit because `termStatic` receives the rank callback as
an argument. The module does not assume a whole imported `CheckedSound` law.
The symbolic index modules supply backend inverse results separately.

`join_public_checked`, `frequency_public_checked`,
`enumerated_public_checked`, and `imported_public_checked` instantiate the
public `CheckedRankQueries.CheckedSound` interface. Kernel examples reject
wrong join components and extra center keys while preserving repeated
frequency members. No Haskell defect was found in these flag producers.

The finite join and frequency children use the modeled finite `Source`
fragment. Recursive flag producers, arbitrary recursive nesting of composite
callback objects, and the host `Int` position representation remain separate
adapters. The proofs use the existing typed natural-rank and private-label
representation. They do not claim a whole-library extraction theorem.

Validation on 2026-10-12: pinned Lean 4.34.1 builds
`MicroCFTA.CompositeCheckedRanks` with 76 jobs. No additional axioms, `sorry`,
or `native_decide` are used. No Haskell source changed.
