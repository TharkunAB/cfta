# Checked optional-binder series review

Reviewed on 2026-10-17 at 06:42 CEST. No material defect was found. No production file was changed during this review.

The final source is `SourceCurrentAllocatedRecursiveMassCheckedSeries.lean`, SHA `a67ba3a804478833ade6f8e4948d6b6a7e9c843e41db95819e57e7bade3dc2fd`. The six public declarations are `code`, `replaceHeap`, `code_fields`, `same_tables`, `trace`, and `complete`.

`code` emits one literal optional-binder instruction for each input key. Each continuation consumes the preceding returned body. `replaceHeap` changes only the constructor heap. `same_tables` retains the complete node table, edge table, domain cache, and equality-operation state by definitional equality. It does not assert equality of the whole native machine, whose constructor heap can grow.

`trace` follows the supplied source series return. In each nonempty case, an actual pending first call contradicts the supplied final return. A completed first call supplies its own facts and available result. The induction uses that exact result and heap. Its checked `Trace.cons` records the current body availability, the literal yielded step, and the exact remaining trace. This helper takes a completed source run; the public `complete` endpoint constructs that run itself.

`complete` takes only the initial checked `Good`, semantic constructor `Context`, available initial body, decoded depth heap, and `Covered []` heap. The source series completion derives every later semantic context, depth heap, coverage, and available result. The same source run supplies the checked physical trace. `code_fields` and `RecursiveAllocationTrace.prefix_bound` retain `Good` at its actual endpoint. There is no initial callback law, successful series, intermediate mass bound, later capacity, or desired result premise.

The resource schedule starts at `initialBound` of the original series-entry constructor heap. The node and edge bounds use one `credit keys.length` computed from that bound. They do not read future counters. The final causal store uses the corresponding `massAfter`. The schedule does not pay for source construction before series entry. The numeric ceilings remain symbolic in all imported checks.

## Independent imported kernels

`two_calls_exact` invokes the checked `complete` endpoint from arbitrary initial populated checked tables and legitimate initial facts. It separately constructs a source series return from the same initial facts. Both physical traces give the same bounded checked execution, so determinism identifies their complete returned value and heap. Inverting that source series exposes the literal first call and the second call at the first returned body and heap. The kernel also derives literal `execute 3 = done`: two yielded optional instructions and the final pure return. It retains `Good`, the original numeric credit, exact native/domain/operation tables, and result availability. It assumes no successful call or intermediate state.

`constructed_nested_checked` first constructs its own open nested Mu from empty source storage with two distinct intersection captures. Concrete reduction verifies that both captures occur in the initial body and that the body is a Mu. It then uses `two_calls_exact` at any initially Good checked state whose actual constructor heap is that constructed heap. A second reduction verifies that the second capture remains in the first actual returned body. Thus neither call takes the unused-pair shortcut. Both actual source returns, the two-step physical trace, final `Good`, causal store, counters, exact tables, and available result are retained.

The second kernel leaves the unrelated checked-cache setup explicit: it accepts initial `Good` for the populated checked state. It does not derive that premise from the source constructor alone. The source construction derives its own context, depth heap, coverage, and available body. This distinction avoids assuming a completed future query or introducing unrelated equality-field initialization.

## Validation and limits

The final public log is `mass-checked-series-public-2.log`: six explicit full-signature and axiom pairs. The final integration log is `mass-checked-series-kernels-5.log`: two explicit pairs. Both checks exit zero with no warnings, errors, holes, output truncation, or nonstandard axioms. Public log 1 is retained as an earlier imported check. Integration attempts 1–3 have evidence-only elaboration failures. Attempt 4 passes. Attempt 5 adds the used-second-call observation. Every attempted source and raw log remains unchanged.

The exact final production strict log is `mass-checked-series-direct-3.log`, which is empty. The final canonical copy is `mass-checked-series-final-canonical-audit.log`: the corrected target rebuild and full Audit pass, with 2864 jobs and 63784 dependency checks. Its only warning is the older unused `inputs` binder in `InternedFreshOrdinaryClosedCompletion.lean:24`. The earlier standalone canonical batch and production drafts remain historical validation. The final correction removes one unused simp argument and changes no public signature.

This result constructs a full checked OPTIONAL series only. Its physical length counts atomic optional instructions, not every internal source constructor action. The numeric budget bounds internal node and edge reservations. It does not give a universal running-time bound, full generated-query resource theorem, equality/domain counter bound, all native compiler instruction completion, or general constrained-reduction termination. It changes no Haskell code and establishes no new Haskell defect.
