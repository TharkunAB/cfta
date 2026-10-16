# Actual checked target query

The owned module `lean/MicroCFTA/SourceCurrentAllocatedTargetQuery.lean` is frozen.

## Public interface

`Step left right before value after` records an actual `PhysicalTrace` from `requestNode emptyDomain left right` to the returned pure value and full checked state. Its constructor is `.run trace`. `Step.done` derives a finite literal `execute` receipt. `Step.unique` equates the complete returned state and value of two such steps.

`Receipt formulas solver next left right before value after memos` records the raw step, full current `ClassScan.Ready`, final `At`, physical `Effects`, machine `Extension`, result availability and closedness, exact independent PCS intersection language under every ambient environment, coherence of the SAME three-family global bundle, and real `SourceGlobalUnfold.Runs` with `NoGlobal`.

`finite formulas solver inventory left right before ready admitted leftAvailable rightAvailable leftClosed rightClosed ranges memos valid` constructs `next`, `value`, and `after`. It exposes `next.source = before.native.machine.heap` and `next.roots = inventory.roots ++ [left, right]`. It then supplies the receipt at that actual return. Empty and duplicate operands retain their literal inventory positions.

`Step.verified formulas solver inventory actual ...` uses the same initial premises. It derives a computed next inventory and the same receipt at the supplied raw step's literal output and full state. The proof constructs a completed query, then applies `completed_unique`. The receipt's `actual` field retains the supplied step.

## Premises and proof route

Initial `Ready` supplies physical Good, SemanticReady, stored CostHeap, scoped tables, and idle tables. Initial `At` supplies fixed computed inventory interpretation, all-phase request/seen admission, and source heap/history growth. The operands must be closed and available in the actual entry heap. Reached `WordRanges` and initial global-table coherence remain explicit.

`InventoryState.query_complete` computes the next actual inventory and derives contextual/scope completion. Actual `TraceEffects.effects` derives final physical readiness, equality-operation growth, and machine Extension. `AllocatedNativeGlobalMemos.trace_memos` derives real primitive events and coherence of the unchanged global bundle from this same checked trace. No old scoped native execution is substituted.

No final validity, NodeProduced, result language, future input plan, or completed callback is an input to the public finite endpoint. The raw `Step` contains reached physical checks; verification of any such step aligns it with the independently constructed completion.

## Validation

Canonical command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedTargetQuery
```

Terminal status: 0, 1233 jobs. `query-build-1.log` preserves output. No new warning. The only replayed warning is the existing unused `inputs` warning in `InternedFreshOrdinaryClosedCompletion`.

Direct public command:

```
LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-checked-target/query-public-probes.lean
```

Terminal status: 0. `query-public-probes-2.log` contains four public axiom checks, four full signatures, and eight kernel examples. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Examples cover the raw physical trace, exact count-plus-one completion, whole-state uniqueness, finite duplicate-empty admission without supplied completion, arbitrary actual-step verification, repeated-operand language, real global silence, and equality-operation retention. The first failed probe only used the wrong namespace for `empty_available`; its raw output is retained.

No compiled artifact was written to the evidence directory. The proof source, public probe, raw logs, and SHA256 manifest are retained.

## Source boundary

The request is the actual checked `SourceEqualityNativeDemand` request, with its original state and actual operation cache. It is not an erasure to the old eager scoped native engine. This component proves finite completion under reached machine-range checks and the stated warm invariants. It does not remove the machine-range condition, establish Haskell lazy operand forcing or global unsafe-IO behavior, or prove whole constrained-caller termination. A target/leaf caller must retain its external merge cache and shared task slots around this exact primitive. Those caches are not reset or modeled inside this query.
