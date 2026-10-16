# Current allocated target worker completion validation

Validated on 2026-10-16. The source is frozen at `018d5ac42ac0a3a062a8abeeb83af446b798d0a0f6e8c1726e1f9fbce9184896`.
The module has 375 lines.

## Checks

- Pinned Lean 4.34.1 direct check passed with no warnings. Final log: `completion-direct-6.log`.
- One focused canonical build passed with 1284 jobs. The process 47811 returned exit 0. The only warning comes from the older `InternedFreshOrdinaryClosedCompletion` dependency.
- All 17 public theorem axiom reports passed. All 18 explicit public signature checks passed. `StableRun` is included in the signature count.
- All 8 integration kernels and 8 explicit kernel signature checks passed. Final log: `completion-kernels-4.log`.
- The 25 final axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. The final public and kernel logs contain no `sorryAx`, error, or warning.

## Established statements

`projection_complete`, `merge_complete`, `operand_complete`, `leaf_complete`, `fold_complete`, and `target_complete` derive five stable sufficient bounds from the corresponding actual completed graph. `target_uniform` derives one shared upper bound. The five fuels are projection, read, merge work, selection, and native execution.

`forest_done_stable` proves direct successful projection stability. Its structural proof covers skipped positions, ordered row traversal, recursive exposure, and union. It uses the existing literal completed exposure stability theorem. The wrapper stability theorems retain the same value, entire checked state, and completed merge table. `target_done_stable` requires only a literal successful return and five fuel inequalities. `target_done_unique` identifies complete successful observations across different fuel choices.

The integration kernels check two-path and three-path source order, exact intermediate merge table continuity, a successful worker aligned with an actual graph, finite target construction from initial invariants, a warm selected hit with an unrelated open sibling, recursive projection stability, native success stability without a fabricated physical trace, and failed-tail termination before the final native request.

## Scope

Graph-to-stable completion assumes an actual finite component graph. The external initial-facts kernel obtains that graph and its full receipt from the existing `TargetComplete.target_complete` theorem. It uses selected-path `ForestClosed`, actual reached `TargetRanges`, initial ready/admission, resident captured values, stored merge entries, uniform language coverage, and initial global memo validity. It does not require whole-forest closedness or a future result law.

Successful native fuel stability does not derive `PhysicalTrace.Inputs`. Physical native soundness remains the distinct initial-check theorem in `SourceCurrentAllocatedTargetWorkerNative` and the conditional soundness module. This module does not convert a failed, pending, unresolved, blocked, or exhausted observation to success. General outer-worker termination, host demand order, and runtime publication remain outside this component.

## Preservation

Only the new completion source and completion-prefixed evidence files were written. No older proof, Audit, restart authority, Git, Haskell, or runtime file was changed. Earlier direct and kernel error logs remain as diagnostic evidence. They are not the final validation logs.
