# Static projection worker fuel review

The frozen production module is `SourceCurrentProjectionNumericReplay.lean`.
Its SHA-256 is `53600902e69c0bfb9d924e2adef0d2f378c0d08fc39584e348c6ce476583411d`.

The worker fuel is `2 * path.length + 1`. It does not depend on a completed graph's recursion count. A nonempty ordinary input needs only `2 * path.length`. The mutual proof derives both facts together. An ordinary selected step consumes one worker unit before projecting the shorter path. A recursive step consumes one unit for Head, then uses the ordinary bound for the same remaining path. The ordinary exposed-value fact prevents an unbounded chain of recursive heads at the same path length.

ReadReady records one exact demanded nodeEdges result and full returned heap at the shared read fuel. ReadAllReady records each literal read and its exact following heap. UnionReady retains the actual makeNode equation. HeadReady retains the actual row read, constructor equation, and Ordinary result. ProjectReady and RowsReady mirror the supplied physical graph. ForestReady keeps root union, missing signed position, and selected root separate. No certificate requires a global closed forest or a closed unselected source value.

All seven certificate families have a public mono theorem. Increasing shared read fuel uses existing nodeEdges stability. It preserves the rows, values, and complete heap. It does not replace the original graph with an execution at a different initial state. The two projection recursors pin the same DecidableEq EdgeKey instance in both motives. This avoids an independent instance metavariable in recursive cases.

The eight replay APIs cover read, readAll, union, Head, project, the sharper ordinary case, rows, and forest. They retain exact ordered results and full heaps. Each accepts any reader fuel at least the shared bound. Project, ordinary, rows, and forest use the static worker threshold. Missing signed forest positions perform no projection or read. The forest theorem's common threshold remains conservative for that branch and for root union.

The final public probe checks 24 declarations with full explicit signatures and axiom reports. The three integration declarations use the same settings. Only propext, Classical.choice, and Quot.sound occur.

The fixture builds the productive raw binder `mu x. step(x) | constant` from the empty constructor heap. It constructs its own actual two-step projection with a small literal successful worker receipt. Private evidence helpers recover the exact read certificates from that actual worker and derive each Head Ordinary fact from the initial physical invariants. They do not accept a computed-fuel projection or a future certificate. The first kernel proves both node and edge allocation and replays the same result and full heap at static worker fuel 5 and every larger shared read fuel.

The second kernel selects that same closed operand beside an unrelated open depth reference. It derives the exact selected-forest certificate and replay. It also checks the negative missing-position branch at zero worker and read fuel. This distinguishes the selected domain from an all-root-closed premise.

The third kernel starts at the first projection's exact returned heap. It derives the physical facts from the first actual graph, then constructs the actual warm repeat and source root union. Both return the same literal result and full heap. The kernel supplies no later-entry invariants or completion assumptions.

Strict production attempt 4 passed with an empty log. Canonical build 1 passed with 766 jobs. Its warning belongs to the earlier ClosedCompletion dependency. The new source and final imported probes have no diagnostics. Public attempt 1 and kernel attempt 3 passed. All earlier sources and raw logs are preserved. Early production attempts fixed explicit edge types, actual constructor witnesses, and the fixed instance in mutual replay motives. Early kernel attempts fixed existential state substitutions and erased proof-index argument annotations.

This is a completed-graph replay component with a static worker bound. ReadReady still records successful shared row reads at the actual demanded sites. This module does not compute that shared read bound from initial resources. The separate initial-resource producer must construct these certificates. General initial selected Operand resources and whole-library convergence remain outside this component.
