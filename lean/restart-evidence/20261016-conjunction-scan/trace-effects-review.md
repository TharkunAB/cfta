# Physical trace effects and native memo retention review

Timestamp: 2026-10-16 06:57 CEST. Read-only source review. No canonical build or proof source edit was performed.

Reviewed root source: `SourceCurrentAllocatedNativeTraceEffects.lean`, SHA256 `4168b87e3db60925ea6ccb04ab0068939ed72b53634d0757b79e5fc13cfd35df`.

Reviewed memo source: `SourceCurrentAllocatedConjunctionMemo.lean`, SHA256 `cba26b96b0bb99358f828dc62cb1175dff76af067acf46199670dfc9386c9c60`.

No material defect was found.

## Trace effects

The `Trace` fuel counts yielded instructions. Its endpoint is the literal code `.pure value` at `after`. `Trace.plan` derives physical `InputsThrough (fuel + 1)` and includes the terminal pure instruction's trivial physical check. `trace_done` uses exactly that additional instruction to prove `execute (fuel + 1) control before = .done value after`. The theorem then rewrites every execution outcome through this same equation. Thus final validity, semantic readiness, costs, fields, equality-operation growth, and machine extension all refer to the exact trace-final state.

The initial premises are `Good before`, `SemanticReady before.heap`, `CostHeap before.heap`, initial control `Fields`, and the actual physical trace. No final invariant, parent language law, contextual law, result scope, or completion callback is supplied. Reached physical checks come from `Trace.plan`; `through_heap` derives the smaller checks used by semantic and cost preservation. `execute_invariants` derives actual returned `Good` and `OutcomeFields`; the final operation validity and loaded equality fields come from that derived `Good`. The constructed physical `Effects` retains the exact before and after equality-operation caches.

The theorem transfers an actual trace. It does not construct one, prove query completion, derive independent result language, or preserve contextual cache laws through a native query. Those claims remain with the corresponding completion and semantic receipts. Initial control `Fields` remains an explicit static annotation premise; it is not a future heap oracle.

## Memo state retention

The exact node state, edge state, and domain cache equalities follow directly from `QueryMemo.advancePhysical` and `advance_tables`. They require no physical effect premise: this adapter only replaces the machine heap and equality-operation state. This includes whole native cell records, their statuses, request metadata, and both table supplies.

Physical validity retention does require initial `Good` and actual physical `Effects`. `advance_good` uses the returned heap facts, unchanged domain-cache validity, and the derived machine `Extension` to transport all old physical cell invariants. It does not infer native result laws from physical validity.

Contextual and scope retention have initial invariant premises. They follow directly from the unchanged returned cells in the same fixed interpretation; no new cache entry or output law is created. Idle retention follows from the same unchanged statuses. `advance_self` identifies the entire checked state for an unchanged physical result, including an actual completed hit. None of these statements claims retention of runtime global memo tables outside the represented native tables and domain cache.

## Direct validation

Command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-conjunction-scan/trace-effects-review-probe.lean
```

Result: terminal exit 0, no warnings. One public axiom report and one signature passed. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Both kernel compositions passed:

1. An actual pure-return trace derives exact done state, final `Good`, semantic and cost heaps, same-cache loaded fields, equality-operation growth, and machine extension.
2. An actual original-operand node request derives result availability through `RequestResults.node_result`, then completes the current conjunction memo directly. Initial memo correctness grows through the actual native effects. Idleness follows from the actual done equation. The composed result retains both physical stages and conservative memo soundness. This example requires no returned language law, future readiness, earlier fourth-memo call, or supplied completed decision.

The second example remains scoped to original operands because `node_result` uses their represented physical key. It does not establish general completion or a fixed-model extension for generated operands. GHC lazy forcing, publication, concrete containers, allocation order, and concurrency remain separate runtime obligations.
