# Raw outer graph reads validation

Date: 2026-10-16 18:47 CEST.

The source is `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryOuterRawReads.lean`.
Its SHA256 is `e3d401b5be355030f7f001cbae52605e9177801f17f281785434dd71bc55ea8e`.
The source has 293 lines. The source snapshot is byte-identical.

## Checks

- Direct source check 4: exit 0. Session 63582 was polled to its terminal result. The log has no diagnostics.
- Canonical build: exit 0. Parent observed session 26806 terminal. The log reports 1538 jobs. Only the historical unused `inputs` dependency warning remains.
- Imported public probes: exit 0. All 8 public theorems have an axiom probe and a full signature probe.
- Imported integration probes: exit 0. All 5 kernels have an axiom probe and a full signature probe. Session 36063 was polled to its terminal result.
- The final public and kernel logs have no warning, error, or `sorryAx`. Reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Direct draft logs 1 and 2 retain failed elaborations. Log 3 passed before explicit public binders fixed the argument order. Log 4 checks the frozen source. Public arguments start with `bits`, `formulas`, and `solver`.

## Coverage

The eight endpoints cover node call, node body, edge call, edge body, rows, descendants, children, and walk. Each endpoint constructs strict reads for the same supplied raw graph and exact returned caller. None takes supplied reads, successful callbacks, Checks, final Context, or a result law.

The induction derives each next Context, residency, domain, and cache certificate from its actual earlier prefix. Rows process edge call, returned-edge descendants, and suffix in order. Walk processes the indexed child and then its suffix. Evaluating calls retain the exact captured owner. Edge bodies use the current parent verifier at the same actual result. Empty and contradiction branches retain the global bundle.

The kernels check raw call verification, two sequential actual calls with the second inventory and global bundle derived from the first, ordered row domain and height, strict returned child rank, and the contradiction branch with no child-call reads.

## Boundaries

The supplied graph must be completed. These endpoints do not construct general outer completion. The numeric entry Plan remains an explicit premise. It supplies capacity at independently reached parent entries. It contains no own-parent completed result or semantic law.

The input domain is finite ordinary syntax. Guards and equality classes remain unrestricted. Mu, explicit union, and reference syntax are excluded recursively. These results do not establish GHC demand order, a runtime allocation trace, or a global finite allocation bound.
