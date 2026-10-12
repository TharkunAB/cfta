# Source fresh declaration domains

`SourceSortedQueries.lean` uses the exact declaration list sent by Entails and
Satisfies: flatten all resolved scopes, collect present declarations, and
remove duplicate pairs. A declaration pair contains the generated name and
the original name from which the backend obtains its sort.

`entry_domain_related` proves that source resolution preserves the original
sort name and the interpreted value of its generated name. `domain_related`
extends this result to the complete source list, including duplicate removal.
`sorted_query_iff` combines the result with the complete query formula proof.
Both directions construct their environment maps from the source fresh table.
The sort-domain function is arbitrary, so this includes the backend's lookup
of a declared sort with the integer default.

This theorem covers generated declarations. It does not identify this domain
predicate with the entire Z3 context. That context also contains ambient
declarations and assumptions, default declarations for free names, contract
declarations, and the name-collision rejection step. These require their own
preservation conditions. The confirmed ambient collision in
`GuardAlphaBoundary.hs` shows why that distinction matters. This module does
not infer exact Yes/Unknown agreement from mathematical equivalence.

Validation: `lake build MicroCFTA.SourceSortedQueries` succeeds with the pinned
Lean toolchain. No production source changed.
