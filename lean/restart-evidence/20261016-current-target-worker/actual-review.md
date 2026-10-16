# Independent target-worker actual-return review

Reviewed `SourceCurrentAllocatedTargetWorkerActual.lean` at SHA-256
`a3f95f306e6c583b697fe2617b1af10298a813c2a92626270d8ddd706a3c5164`.
No material defect was found. No proof source was edited.

## Exact return and inventory

`verified` passes the supplied worker success to `target_sound`. That
theorem extracts the actual projection, allocated merge, and native returns.
The native bridge derives physical checks from initial Good, idle cells,
closed resident operands, and reached ranges. It does not assume a physical
trace from an arbitrary native success. `Target.verified` then verifies this
same graph. The result, checked state, and saved merge memo remain the
supplied return. No independently completed target replaces that return.

`finite` obtains an actual graph from `TargetComplete.target_complete`.
`TargetWorkerCompletion.target_complete` supplies stable bounds for that
same graph. The returned inventory is the inventory from the actual graph
receipt. `caller` and `caller_finite` use its `admitted` field at the literal
returned checked state. They do not reuse initial admission at a changed
heap or require a future inventory or cache law.

## Caller state and language

Both caller endpoints use
`PartialState.advance before after before.fourth saved`. This retains the
complete node and edge result tables and the same fourth memo. The checked
state and completed merge memo are the actual returned values. Initial
warm result-cell laws survive through `Sound.advance` and the actual physical
Effects. The same Effects retain fourth-memo correctness. Probe validity
comes from the read evidence for the actual graph, not a final probe premise.

The initial Context explicitly contains physical readiness, inventory
admission, warm outer-cell laws, merge residency and language coverage,
fourth-memo correctness, global coherence, and probe validity. The public
endpoints preserve this legitimate warm context. They do not construct it
for arbitrary warm tables. Selected-path domains and reached ranges remain
explicit. Unrelated original siblings need no whole-forest closedness proof.

The target language conclusion is conditional `Includes`: a nonempty list
of nonroot selected paths preserves their common accepted subtree. It is
not exact target-language equality. The allocated merge can overapproximate.
No same-parent output law or accepted candidate is a completion premise.

Global Effect records are derived logical read receipts. The executable
worker does not manipulate a concrete host global table bundle. The header
states this limit. GHC demand order, lazy publication, native Set/IntMap/
HashMap correspondence, and the full outer worker remain separate.

## Imported validation

The root reported canonical target success in
`actual-shared-completion-build-2.log` with 1304 jobs. The independent command
was:

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-target-worker/actual-review-public.lean
```

Final log: `actual-review-public-2.log`, exit 0, no warning.
It checks four public axiom sets and full signatures:
`verified`, `finite`, `caller`, and `caller_finite`.
All use only `propext`, `Classical.choice`, and `Quot.sound`.

Two external kernels pass. The first calls `caller_finite` for two proper
paths, extracts five literal execution bounds, and derives an actual worker
success. Its same-return Post retains both outer tables and fourth-memo
correctness. It also derives the conditional selected Includes conclusion.
The second checks literal zero-bound empty-target success and the unchanged
caller state. The first probe log records one elaboration failure in that
empty case. The final probe adds explicit empty path and bound arguments.
It changes no proof source or theorem statement.

No canonical build was run for this review. No owned process remains.
