# Independent active-frame review

Reviewed at 2026-10-16 15:12 CEST. No material defect found.

Reviewed source: `SourceCurrentAllocatedPartialActiveFrames.lean`, 224 lines, SHA256 `eb36338be4460529d7ad7991c95bd2d11bd6eb9a7c9064fcf5998348786d78d7`.

## Exact statement

`NoNewActive` at lines 24–26 has reverse `Running` in both result tables: every final evaluating cell, with its exact stored request and handle, was evaluating initially. It does not assert that every initial evaluating cell survives. `NoNewActive.trans` at lines 33–35 composes in the correct reverse order.

`NoNewActive.activeExcept` at lines 44–48 retains arbitrary bounds and both excluded handles. It applies the initial bound to each final evaluating owner through the reverse frame. No protocol, semantic law, result height bound, initial readiness, or future completion premise appears in this theorem or the eight completed-graph endpoints. This absence is correct. Reverse active-cell inclusion is weaker than forward survival of old cells. Forward survival and exact owner readback still use the separate `PartialFrames.Protocol` results.

## All sixteen graph constructors

The mutual recursor at lines 138–180 has all sixteen cases:

- Node hit and edge hit trace the ready demand back through literal publication.
- Node evaluate and edge evaluate exclude their finished handle with `finish_not_running`, trace the other final cells through the actual body, and then trace demand and publication back to the initial table. They preserve the exact other-family component.
- Empty and union node bodies are reflexive. A completed Mu reconstruction advances lower state and retains both result tables. Ordinary rebuilding composes the actual row frame with the constructor's unchanged outer tables.
- The parent edge body advances the exact checked, merge, and fourth state. It leaves both outer tables unchanged.
- Empty rows are reflexive. Nonempty rows compose edge narrowing, descendants of the returned edge, and suffix in that order.
- Descendants compose the inherited prefix, actual child graph, and raw rebuild. These lower-state operations do not change outer tables.
- Contradiction children are reflexive. Live children use the literal indexed walk.
- Empty walks are reflexive. Nonempty walks compose actual descent, head node call, and suffix.

These cases match `PartialGraph` and the literal worker. Source `Equality/Operations.hs:80–96` memoizes before node body evaluation and maps parent reduction followed by descendants over each returned row. The theorem concerns the completed serial model. It does not specify GHC thunk forcing, concurrent publication, black holes, or host cache operations.

## Imported integration checks

Twelve public axiom/full-signature pairs and the `NoNewActive` structure signature passed. Four independent integration kernels passed:

1. A supplied literal node-worker success derives its own completed graph, strict reads, full same-return `Post`, reverse active frame, and restored arbitrary `ActiveExcept` bound. The input has no completed graph or future state law.
2. Literal owner publication, an actual completed body, and exact owner finish restore the parent bound. The kernel uses the separate forward protocol frame to prove that the same original owner survives the body and receives the returned result. Reverse inclusion alone is not used to infer survival.
3. Actual rank push admits a smaller recursive bound. The completed body retains that bound, and finishing restores the stronger parent bound. The local completed body remains explicit; this is not a proof that it exists for every request.
4. A literal edge-worker success followed by literal descendants of that returned edge restores the original ancestor exclusions before a later sibling. Both prefixes derive their own graph and `Post` at the exact returned states. No suffix success or future invariant is assumed.

All final direct checks returned exit code 0 with no warning, error, or `sorryAx`. The only axioms are `propext`, `Classical.choice`, and `Quot.sound`. The source hash remained equal to the frozen hash.

## Remaining boundary

This closes active-bound restoration after an already completed prefix. It does not establish general recursive completion or a structural bound on newly returned edge height. `PartialActiveOrder.ReturnedBounds` at lines 304–306 is separate. In particular, a semantic narrowing law does not itself prove that local constrained reduction preserves that height. A later termination proof must derive its structural progress facts and actual body completion without assuming their conclusions.
