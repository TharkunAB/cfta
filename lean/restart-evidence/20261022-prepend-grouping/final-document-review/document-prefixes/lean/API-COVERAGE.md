# Public API and source correspondence

## Ordered symbol buckets for later group traversal

Updated: 2026-10-22 23:33 CEST. Proof checkpoint: `44fcfd7d89`.
Start: `d0cf685f46`. Imported main remains `794903b3f`.
Read `lean/notes-current-prepend-grouping.md`.

The selected SourceCurrentPrependGrouping declarations establish the reviewed
pure singleton-prepend, final reversal and finite iterator bridge.
Keys use equality. Each normalized bucket keeps its full input order and
all repeated occurrences. The outer bucket order remains unspecified.
The proof retains absent versus stored optional buckets.
It reuses the existing generic ordered grouping and iterator contracts.
This is not a refinement of Haskell HashMap storage or lazy evaluation.
No actual all-symbol traversal or new state/resource producer is claimed.

H20 preserves physical union language for one original symbol group.
All-symbol traversal, reconstruction, generated parents, public Mu/full pass,
practical width, solver contracts, Haskell refinement and convergence remain open.
H6 constructed_node_calls remains the strongest combined semantic theorem.
Preservation covers 93582 baseline files/modes, 298 baseline Haskell files
and 207 active package files. FINDINGS keeps its repair index FIRST.
The approved 12-commit payload was pushed and verified at 562120d456.
Eight newer local commits at the H21 start need fresh exact-payload approval.
This checkpoint stays LOCAL_ONLY and performs no network command.
