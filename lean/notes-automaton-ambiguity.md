# Automaton overlap checks and distinct compact counts

`AutomatonAmbiguity` follows `Automaton.ambiguous`: compare each edge with
every later edge, require equal symbols and arities, then test all paired
child intersections. `ambiguous_false` identifies the complete pair scan.
It does not assume the scan finds every relevant pair.

`common_detected` proves that a shared accepted term makes the overlap test
true whenever the child test retains common terms. This remains valid with
edge guards. Constraints can make the test conservative. A false test still
proves disjoint languages. For plain edges, `plain_overlap_exact` constructs
the shared child tuple and proves the converse.

`productiveRows` models the source empty-row check and minimum-size table
lookup. `productiveRows_covers` derives its negative soundness from the
actual minimum-size worker. `productiveRows_witness` derives a finite term
for plain graphs. `table_test_covers` and `table_test_witness` compose those
workers with the exact synchronous intersection construction.
`table_gate_disjoint` thus obtains disjoint edge languages from computed
intersection minima, including cyclic graphs. It assumes no child overlap
oracle law. The explicit finite state domain must contain every graph state.

`compact_nodup` derives a duplicate-free concatenation from the passing gate
and locally exact, duplicate-free edge callbacks. `compactIndex` contains
all and only the accepted alternatives. Its `Fin n` inverse laws follow from
`DistinctRank.Index`. `compact_count` derives addition of local counts.
The lists in this statement specify callback outputs. They do not require
the source decoder to enumerate all outputs.

The current finite source uses nonempty interned intersections as its
conservative test. The recursive plain source uses `minimumSizes` through
`productiveRows`. The latter is instantiated here with explicit graph
intersection. Interned intersection-to-row readback and the acyclic
smart-constructor productivity invariant remain their source adapters.
The local compact edge compiler, direct-child grouping, callback rank order,
and canonical class ordering are separate operations. This module does not
claim their correctness from a passing overlap test.

Validation: the pinned Lean build passes. No Haskell source changed.
