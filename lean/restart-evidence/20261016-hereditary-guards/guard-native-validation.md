# Native hereditary guard producer validation

Time: 2026-10-16T22:59:57.829866+02:00.

The five production modules are frozen. All 31 public axiom reports and full explicit signatures pass. The public sources enable explicit arguments, full names, universes, deep terms, proof printing, and 10000000 printer steps. All three integration axiom reports and full signatures pass. Direct final logs have no diagnostics or `sorryAx`. Canonical logs contain only the historical unused `inputs` dependency warning.

| Module | Public pairs | Final direct log | Canonical log and jobs |
| --- | ---: | --- | --- |
| GuardStored | 15 | guard-stored-direct-1.log | guard-stored-code-build-1.log, 1116 |
| GuardCode | 7 | guard-code-direct-2.log | guard-stored-code-build-1.log, 1116 |
| GuardBody | 4 | guard-body-direct-1.log | guard-body-merge-code-build-1.log, 1163 |
| GuardExecution | 4 | guard-execution-direct-1.log | guard-execution-merge-build-1.log, 1320 |
| GuardFinite | 1 | guard-finite-direct-1.log | guard-finite-build-1.log, 1174 |

Each public final log is `guard-<part>-public-1.log`. The final integration source is `guard-execution-kernels.lean`. Its final log is `guard-execution-kernels-1.log`. All commands used pinned Lean 4.34.1 and both unused-variable linters. This component ran no Lake, Haskell, or Git mutation.

## Integration checks

1. `cold_repeat_generated` derives structural, shape, guard, and idle invariants from literal initial native tables. It constructs the first query, an independently constructed repeat, and a third query on the first output. The completed-memo trace theorem and full-state success uniqueness prove that the repeat returns the same value and the identical checked state. The third guard profile is `step (step G)`. Its shape and counter headroom follow from one initial reservation. No later profile, count, capacity, completed body, or result law is an input.
2. `warm_node_trace` constructs a literal one-step physical hit trace from actual lookup and demand equations. It derives the stored guard profile at the same full checked state. It also derives literal execution with fuel two.
3. `edge_trace_budget` applies the edge guard producer to the same supplied actual trace that the native budget theorem counts. Its constructor bounds follow from the initial input profile, height, and capacity. It has no supplied returned guard profile or counter bound.

## Scope and proof review

`GuardStored` records universal conditional certificates for exact returned node and edge cells. Both antecedents require empty `seen`; arbitrary seen domains can produce references. Lookup, demand, and advance retain the exact stored requests. Finish accepts a local producer certificate only for the selected evaluating owner.

`GuardBody.body_certified` derives the combined root guard from actual field loads, cached field readiness, and `AcceptedLanguage.ready_readback`. It then applies the literal conjunction bound. All descendant requests start from the original common `G`; they do not recursively iterate `step` by height. Rejected sentinel guards use the Top bound.

`GuardExecution` proves each result certificate before the exact owner finish. It retains both native guard tables across the actual trace. Warm readback uses current physical validity and exact request equality. The generic code interpreter has an explicit code certificate input. The principal node and edge trace endpoints derive that certificate from their initial guard profiles.

`GuardFinite.finite` constructs its own actual receipt through the existing finite query theorem. It interprets that same receipt trace. It retains every earlier conclusion: physical receipt, result residency, idle state, semantic readiness, structural and shape stores, shape, both height bounds, closedness, capacity, and actual counter bounds. It appends the guard store and output guard profile.

This proves finite-ordinary native query guard production with arbitrary guard syntax and an empty seen domain. It does not prove an initial whole outer reduction reservation, recursive-value completion, GHC demand correspondence, or shared-slot guard production.

## Preserved attempt

`guard-code-direct-1.log` records an isolated import-path failure. Its temporary package path could not resolve GuardProfiles. The source did not need a logic change. `guard-code-direct-2.log` uses the canonical import path and passes. Both the failed log and its exact source snapshot remain present.
