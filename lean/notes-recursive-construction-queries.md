# Queries during recursive construction

The source rebuilds a `recur` or `recurGrouped` body for counts, sampling,
support, terms, and diagnostics. Before the repair, `support self` exposed
`EmptyNode` in count and term rebuilds and a live reference in the support
rebuild. A callback could choose different bodies. Its bounded generator
then returned four terms that its own support rejected. The existing
recursive-member case in `GenSpec.hs` retains this callback.

`Recursive.recursiveConstruction` records active construction tokens. It is
separate from size-index occurrence flags. Closed probes deliberately clear
some size flags; they still represent unfinished construction. Every
placeholder therefore keeps its construction token in every rebuild.
Static sources and imports start with an empty set. Maps, labels, and pays
preserve the set. Applications, choices, and joins combine their input sets.

Completing a definition deletes only its own token. A completed nested
definition retains every active enclosing token. A mutual family combines
the tokens of all probed bodies before deletion. The unused-occurrence
return path also deletes the completed token. This last rule matters when
an outer definition selects a closed key from an inner recursive family.
The selected record can contain a conservative family marker although its
size index does not reach the outer occurrence.

Queries of support, inspection, size classes, minimum size, ranks, terms,
and exact class probabilities reject active records with
`QueriedRecursiveOccurrence`. Grouped count and mass queries check their
actual records. Existing negative-rank errors keep precedence. Queries
without an error result return their existing empty result. Whole-language
cardinality and sampling already reject cyclic records as unbounded.
`atomic` and `upToSize` use construction tokens and retain
`BoundedRecursiveOccurrence`.

`RecursiveConstructionQueries.active_exact` proves that marker operations
retain exactly the unclosed occurrences in constructor provenance.
`family_outer` and `nested_completion` prove nested deletion and retention.
`phase_independent` proves that every marked placeholder gives the same query
error for arbitrary phase-specific payloads. `completed_query` derives
query readiness from closed provenance. `finish_payload` preserves every
generation field. The retained old observation has a checked counterexample;
the repaired observation selects the same callback branch in every phase.

`RecursiveCompleteConstruction` connects these markers to the primitive input
inventory of the complete typed body. Maps, pays, labels, names, flat choices,
plain application, and heterogeneous joins derive the source marker operations.
Family completion keeps exactly the enclosing tokens reached by those bodies.
Top-level completion derives an empty marker set. `support_query_exact`
then composes the repaired query check with the existing exact finite-term
support theorem. It uses the same checked body as the runtime and inverse
records.

This theorem concerns the explicit construction markers and guarded query
operations. It does not prove regularity of every Haskell callback.
`groupKeys` exposes the current key discovery approximation. The grouped
fixed point still requires the documented finite key domain and the source
callback's monotonicity. Haskell bottom, direct internal record inspection,
and fresh machine token allocation remain representation contracts. A
fixed typed body proof does not establish those contracts by itself.

Validation: `/tmp/mcfta-construction-query-full.log` records 620 passing
examples. After the unused-occurrence correction,
`/tmp/mcfta-construction-query-final.log` records all 194 generator and 142
refinement examples passing. Core source was unchanged. The focused repaired
callback returns the single value 99, and its term belongs to its support.
The selected-key regression checks queries, support, diagnostics, and rank
inversion after the outer definition completes.
