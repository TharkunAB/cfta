## Ready same-symbol comparisons

Updated: 2026-10-22 02:39 CEST. Proof checkpoint: `3dfc7e9cd1`.
Start: `f985c09f5b`. Imported main remains `794903b3f`.
Read `lean/notes-current-same-symbol-edge-ready.md`.

SourceCurrentSameSymbolEdgeReady.ready_complete derives execution from an
incoming Stable packet, current heap coherence, both requested resident
edges and presence of the original or reversed pair key. It returns the
actual value and full state at fixed execute fuel 7. The full checked state
is unchanged. The result is resident and satisfies the exact canonical
emptyDomain contextual EdgeLaw. Final Stable, table Extends and Returned
retain the pair memo. Original hits stop in 3 steps; reverse-only hits use 7.

The fixed view, model, ranks and holds remain unchanged. Captured operand
identity follows from resident records and coherence. No execution or
semantic symmetry, native Receipt or native admission is assumed on hits.
Both-miss native admission and completion remain separate H8 obligations.
H6 constructed_node_calls remains the strongest combined semantic result.
Full public-pass behavior, convergence, practical host bounds, external
solver composition and Haskell refinement remain open.

All old proofs, drafts, counterexamples and optimized code remain.
Preservation covers 80323 baseline files/modes, 292 unchanged baseline
Haskell files and 207 package files. New H10 Haskell archive copies must
match baseline bytes. Only the Audit import and additive doc prefixes may
change old files. FINDINGS keeps its Haskell repair index FIRST. Work continues.
