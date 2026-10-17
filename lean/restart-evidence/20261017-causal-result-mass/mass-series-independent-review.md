# Serial generated optional-binder resource review

Reviewed on 2026-10-17 at 06:38 CEST. No material defect was found.

The reviewed source is `SourceCurrentAllocatedRecursiveMassSeries.lean`, SHA `521b7186717669eb920ebf8c06b827fa4a4bc49aadf0eca801d04443ef0b6d74`. It has nine public declarations and 140 lines. The checked-code correspondence is a separate module and is outside this review.

The actual `run` at lines 24–26 passes each returned value and heap to the next call. It does not restart from the original body or an empty heap. `massAfter` and `credit` at lines 29–36 depend only on the initial common mass bound and the number of calls. Their addition laws at lines 45–64 use the exact intermediate numeric bound. They do not inspect an intermediate result or counter.

`run_bound` at lines 67–100 covers every actual stopping outcome. The pending branch retains the first actual returned store, widened to the full series bound. The successful branch gets available inputs and physical facts from the actual first call. It passes that call's produced store to the shorter list. Counter bounds add actual earlier charges. `Verified` retains physical facts, heap growth, and issued-node history. No successful run, callback law, later input mass, or later-entry capacity is an input.

`finish` at lines 103–117 constructs each actual successful call from initial `Context`, body availability, `DepthHeap`, and `Covered []`. It derives the same facts at each literal returned heap. `complete` at lines 120–138 combines that construction with the computed initial heap bound and the all-outcome resource proof. It does not accept a completed execution. It retains semantic context, depth heap, coverage, result availability, full causal mass store, counters, returned mass, heap growth, and issued-node history.

The imported public probe checks all nine full explicit signatures and axiom sets. The two final integration kernels use an actual open nested Mu source with two pair captures. The source construction derives its own context, depth heap, coverage, and body availability. It does not assume the constructed result.

- `constructed_two` calls the public `complete` endpoint for two distinct keys. It inverts that same returned execution to expose both literal call states. It verifies that both pair names occur in the initial body and that the second pair still occurs in the actual first returned body. Thus the second call uses a generated input and does not take the unused-pair branch.
- `constructed_credit` independently constructs a two-call prefix and a one-call suffix. The suffix uses the actual prefix result and heap. Its mass proof uses the prefix's produced `massAfter 2` store, rather than a new assumed bound. The two addition laws combine that exact common numeric bound. One initial `credit 3` word-limit condition derives both the suffix-entry room and final counters. There is no later-entry room premise. The third key can be unused; the first kernel independently checks both used calls.

All `ceiling`, `massAfter`, and `credit` values remain symbolic. The concrete reduction checks only the small source and the first actual optional-binder result. The numeric credit begins at the produced source heap immediately before the optional-binder series. It does not also pay for the earlier source construction.

Public log 1 and integration log 4 have no diagnostics and use only `propext`, `Classical.choice`, and `Quot.sound`. Canonical build log 1 completed 1188 jobs. Its only warning comes from the older `InternedFreshOrdinaryClosedCompletion.lean:24` unused `inputs` binder. The final production strict log is empty. All failed integration drafts remain unchanged. Attempts 1 and 2 had evidence-only elaboration issues; attempt 3 was clean. Attempt 4 adds the stronger nested-source and used-second-call checks.

This theorem constructs a finite series of optional binders. It does not construct all other instructions in a general recursive checked query. It does not prove general generated-query resources, equality/domain counter bounds, or constrained reduction termination. Those boundaries remain separate.
