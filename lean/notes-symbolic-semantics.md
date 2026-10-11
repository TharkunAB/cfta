# Symbolic driver semantic proofs

The new modules use the executable definitions in `SymbolicDriver.lean`.
They do not replace the source decoder with a materialized reference index.

## Normalization and solver requirements

`SymbolicNormalization.lean` proves the meaning of successful `inline`,
`follow`, `rename`, `normalizeTarget`, `normalizeObligation`, and `normalize`
calls. `normalize_solution_iff` preserves domain tests, bindings, and all
pending requirements under the compact variable assignment. The proof includes
missing paths, self-equality, operand ordering, sorting, and deduplication.
`normalize_none_rejects` proves that a failed path rejects the old solution.

`normalize_preserves_graph_domains` retains the graph identities in their
original order. `normalize_fresh` proves distinct compact names and a fresh
next-variable supply. `occurs_constructor_reject` proves the actual occurrence
test cannot reject a finite solution. `constructor_obligations_semantics`
proves the constructor decomposition used by `unify`.

`SymbolicSolutions.lean` defines finite live tuples independently of the
counter. `normalize_count` proves exact count preservation under the source's
empty or one-binding normalization invariant. It also proves the independent
product count and the zero-count path and occurrence branches.

`SymbolicBijections.lean` proves that these tuples are distinct and gives a
finite relation cardinality theorem. `SymbolicMerge.unify_variables_count`
uses it to prove the exact delete/intersect/insert/binding update. Other
pending correlations remain in the theorem.

`SymbolicScope.normalize_scoped` proves that successful normalization leaves
only live names in pending requirements. `SymbolicExpansion` uses this result
to extend old assignments with fresh child names without changing earlier
requirements. `expand_component_count` proves a bijection for the exact
sorted-domain, binding, and edge-obligation update. Each raw equality
component has its own selected-variable language. Components can contain
terms rejected by the original guard before signed cancellation. The proof
does not assume these terms belong to the original node language.

## Counts and caches

`SymbolicCounting.lean` proves graph and context cache lookup/store safety
under explicit semantic cache invariants. `countUnion_distinct_terms` connects
the actual stateful signed fold to the number of accepted distinct candidates.
Its recursive edge-count and exact-intersection premises remain explicit.
`solveStep_independent` proves the actual independent-domain product branch.

The complete mutual `countNode`/`solve` correctness theorem remains open.
`CountSound` in `SymbolicBounds.lean` records this exact remaining contract:
every successful count returns the graph cardinality and preserves the cache
invariant.

## Source decoder and inverse

`SymbolicSelection.decoder_inverse_mutual` proves that the three actual
selection functions invert through the three actual inverse functions. The
proof covers block skipping, child order, singleton shortcuts, and identical
cache flow. It holds for every successful bounded run. It does not assume
semantic count correctness. The inverse returns the input rank minus the
unconsumed suffix.

`SymbolicBounds.decoder_bounds_mutual` proves the residual stays below the
final graph cardinality, assuming `CountSound`.

`SymbolicMeaning.lean` supplies the semantic composition. Its `FiniteMeaning`
interface requires distinct finite graph languages, exact constructor
conditioning, and subtree projection coverage. Projection need not be exact.
`singleton_decoder_meaning` proves the actual singleton decoder correct.
`decoder_meaning_mutual` proves all constructor and child restrictions retain
the selected subtree and all earlier selections.

`selected_root_exact` derives a singleton final language and residual zero.
`unrank_sound_and_inverse` proves that every successful public decode is
accepted and has its exact original inverse rank. `unrank_injective` excludes
two successful ranks for one term.

`source_rank_bijection` proves every accepted term has exactly one actual
source rank in `Fin n`. It additionally requires `DecodeTotal`: every in-range
bounded decoder call returns. This is a termination/error contract. It does
not assume membership, uniqueness, or completeness of the returned terms.

The remaining top-level assumptions are therefore graph-operation
correspondence, complete mutual count correctness, and decoder totality with
a sufficient bound. `SymbolicGraph.lean` proves the declarative conditioning
and projection operations. Interned identity correspondence remains separate.

## Progress and freshness

`SymbolicProgress.lean` proves that whole-variable intersection and variable
expansion strictly decrease a summed structural graph budget. It proves that
normalization preserves this budget, insertion and expansion preserve distinct
live names, and a fresh expansion cannot create a cyclic binding.

The graph budget must decrease from a parent to its complete child tuple.
Intersection must not increase a retained domain's budget. These are structural
graph premises. The full lexicographic measure for constructor/path work and
the universal sufficient execution bound remain open.

These modules build with Lean 4.34.1. The proofs use no added axioms, `sorry`,
or native evaluation. The finite-rank existence proof uses Lean's standard
classical choice principle.
