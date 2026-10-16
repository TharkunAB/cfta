# Current plain child induction helpers

Timestamp: 2026-10-16 15:48 CEST.

The source is `lean/MicroCFTA/SourceCurrentAllocatedPartialPlainChildren.lean`.
Its SHA-256 is `8006e6362dd23104584fd32ed44440ba1c9863d827783dfd50ceae9c43e803ef`.
The source has 116 lines. The frozen copy has the same bytes.

The public `walk` and `children` endpoints construct the actual current graphs and strict read receipts. They return reached checks, the full computed-inventory `Post`, resident output values, and the structural returned-edge domain. Every live head uses the literal allocated descent at its current index and current caller. The suffix starts at the exact returned head state. The actual completed head frame restores the original active-owner bound before the suffix.

Both endpoints are explicit induction helpers. `Below formulas solver budget rank` supplies completion only for requests with strictly smaller `nodeRank`, at callers that satisfy their own initial invariants. The final node-rank theorem must derive `Below`; this module does not assert it. The initial full context, ready inherited allocation, available original values, plain regions, smaller ranks, stored returned-edge domain, and `ActiveAbove (rank - 1)` remain explicit. Contradiction uses the literal erasure branch and does not evaluate the induction hypothesis. The uniform public signature still includes that hypothesis.

The root canonical build passed with 1509 jobs. `children-build-1.log` contains the raw output. Its only warning comes from the older `InternedFreshOrdinaryClosedCompletion` dependency. The final direct source check is `children-direct-2.log`; it passed without output. The first check records the use of a reserved Lean token as a local name. That local name was changed before source freeze.

The final external check is `children-checks-2.log`. It passed with exit code 0 and no errors, warnings, or `sorryAx`. It contains two public axiom reports and two full signatures. It also contains three independently checked integration theorems, each with its own axiom report and full signature:

- A constructed indexed walk obtains its language law from the strict actual-read induction. It retains output length and the initial active-owner bound.
- A constructed two-child graph narrows each original forest and preserves accepted forests that satisfy the actual combined parent constraint. It returns exactly two child slots and the full computed-inventory `Post`.
- An empty walk at rank zero constructs its result without any child-completion hypothesis. The proof discharges `Below 0` by the impossible strict rank inequality and inverts the actual empty graph and its read receipt.

The first external check records a failed finite-list membership simplification and its temporary elaboration placeholder. The final log contains no placeholder. The source module did not change during these external checks.

The module does not prove the whole node-rank induction, general termination, host demand correspondence, or concrete runtime publication. It does not transfer an older caller execution or assume a future parent law, future invariant, or whole future child walk.
