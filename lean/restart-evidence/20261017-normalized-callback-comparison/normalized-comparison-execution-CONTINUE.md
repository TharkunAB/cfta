# Normalized comparison execution continuation

Updated 2026-10-17 19:32 CEST. The component is complete.

Owner: guard_inventory. Current source is
`lean/MicroCFTA/SourceCurrentNativeNormalizedComparisonExecution.lean`.
Latest immutable strict snapshot is `normalized-comparison-execution-direct-15.source.lean`.
Its raw log is empty and exit code is 0. Canonical1 passed with 559 jobs.
The source is frozen at 9d2f9e64c62396b76e32c76428369188fc09371c1b19e100f8c0ca79b80e1a00.

The new Execution source proves private empty, variable, and ordinary-node cases.
It also proves `strip_callback` and the full `ordinary_compared` helper.
The latter compares actual raw ordinary callback calls at different arguments.
It lifts finite varying labels, proves both fixed-capture freshness conditions,
transports no-deep occurrences, invokes the smaller source comparison, and
returns exact ordered stripped alternatives after actual callback filtering.
No output comparison premise other than the smaller syntax induction is used.

The core `SourceCurrentNativeNormalizedComparison.lean` is frozen at c432a1f0.
Its canonical build passed. `Compared` is only an induction specification.
Finite, Inactive, Union, and NormalizedErasure dependencies are frozen and canonical.
Root owns Union and the forthcoming Candidate law module.
Arity owns a forthcoming completed-binder decomposition helper.

The following proof sequence is now complete.
Prove `binder_compared` using private `MuHeap common`.
Split inactive source support via `inactive_compared`.
For live support, `binder_unused` gives smart=true and unused probes.
Actual RequestProbes plus actual growth places the chosen Mu in common.
The private MuHeap law rewrites each return as eraseSelf of its ordinary probe.
Then use `ordinary_compared` with the actual raw ordinary callbacks.
Instantiate its smaller Compared premise from structural recursion on body.

Then prove private `source_compared` for all syntax by structural recursion.
Finally establish MuHeap along actual MuPublication.History by induction.
Depth, ordinary, and body subhistory induction establishes MuHeap at afterBody.
Use root Candidate helper and private source_compared to prove candidate law
BEFORE keepFirst; preserve older winners through the actual table update.
The public endpoint must construct the closed history and must not accept
MuHeap, future callback equality, or an assumed returned origin as input.

The final public endpoints are `history_unused`, `closed_unused`, and
`closed_compared`. The private MuHeap premise is discharged by causal History.
The public stored laws accept no assumed callback equality or output law.
The comparison retains initial contexts, finite slot coverage, freshness on
both assignments, first-run no-deep observations, and actual common-heap growth.
The whole outer recursive termination and native physical-history adapter
remain separate obligations. No Haskell change or new Haskell defect is claimed.
