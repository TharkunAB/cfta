# Checked query constructor Work trace

Validated 2026-10-16 20:39 CEST.

`SourceCurrentAllocatedFiniteOrdinaryQueryWorkTrace.step_trace` records one literal yielded instruction. `prefix` records every actual yielded prefix. The public prefix arguments match `QueryReservations.prefix_counts`: bits, source, valid, fuel, control, next, before, after, origins, certificate, actual.

The resulting `ConstructorWorkTrace.Trace` uses the exact initial and returned constructor heaps. Its request list is exactly `QueryReservations.requestsThrough` at that supplied raw prefix. A Work instruction uses `Trace.work`. Node lookup, edge lookup, demand, finish, and checked edge-body instructions preserve the complete constructor heap. A checked body can change the equality operation state. The static certificate excludes enter, read, and optionalBinder instructions. `WordExecution.step_preserves` supplies the certificate at the next actual instruction.

The proof does not require a completed query, a final invariant, a future word check, a budget, or final capacity. Its initial source validity and original-request invariant have the same role as in `QueryReservations.prefix_counts`. The trace does not count equality-sidecar work, global memos, native table allocation, host allocation, concurrency, or elapsed time.

Validation:

- Direct source check 2 passed with exit 0 and no warnings. Source check 1 is retained. It failed because a heap equality still contained the reducible `Outcome.state` projection.
- Root canonical `query-resources-build-1.log` passed 1267 jobs. It includes this exact source. The only warning is the historical unused `inputs` dependency warning.
- Imported public check 1 passed both full-signature and axiom pairs. The axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- Imported kernel check 3 passed four theorem/signature/axiom pairs without warnings or `sorryAx`. Earlier failed kernel logs are retained.
- The four kernels cover an actual makeEdge step, an arity-mismatch operation-only body, actual finite-ordinary query-prefix Work with an input-only request budget, and two actual consecutive prefixes with the exact intermediate heap and miss equations.

No older source file was edited. No canonical build or Git operation was run by this component owner. No compiled artifact was written into this evidence directory.
