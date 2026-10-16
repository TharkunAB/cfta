# Current mutual caller invariant and primitive effects

Validated at 2026-10-16 11:38 CEST. This increment adds only `SourceCurrentAllocatedPartialInvariant.lean` and `SourceCurrentAllocatedPartialStepEffects.lean`. The two files contain 212 lines. Earlier proof files and Haskell files remain unchanged by this work.

`Context formulas solver inventory caller memos` retains the checked Ready state, input inventory admission, phase-aware caller cell Sound, warm merge Stored and CacheCovers, fourth-memo Correct, actual global memo Valid, and the filtered ProbeHeap. ProbeHeap remains an independent initial representation invariant. The context does not infer it from Ready or Keeps.

`Post formulas solver next before after final` retains the returned Context, physical Effects, merge Extends, and fourth Extends. `Post.trans` permits different computed inventories at consecutive stages. `Context.rebase` and `Post.rebase` apply when checked, merge, and fourth components stay exact. They require a Sound proof for the protocol change. They do not manufacture a returned-cell result law. The external kernel checks derive that Sound through actual publication or exact-owner finish rules.

The four public step helpers derive all their returned facts from initial Context and current concrete inputs:

- `raw_edge` executes the literal raw equal-arity edge rebuild. Its work inputs derive probe preservation. It returns the actual EdgeReceipt and Post at the literal advanced caller.
- `modify` follows the exact ordered edge-identity comparison. Equal lists retain the input. Changed lists use actual makeNode work. It returns the actual NodeReceipt and Post.
- `inherited_prefix` derives the finite resident-field receipt and aligns its exact successful result with the supplied run equation. It combines in inherited-first order at the current equality cache. The returned context uses that literal prefix state.
- `descent` uses the actual indexed allocation receipt and retains the same native and caller tables. It returns Post at the literal descend result.

The implementation uses one private context assembly lemma. Each public step discharges its ready, admission, effects, and probe inputs from the actual primitive. No public helper assumes a final Context, final ProbeHeap, result language, callback success, or completed recursive body.

Focused canonical checks used pinned Lean 4.34.1. Invariant completed 1,239 jobs with exit 0 in `effects-invariant-build-2.log`. StepEffects completed 1,399 jobs with exit 0 in `effects-step-build-2.log`. Only the existing unused `inputs` warning in `InternedFreshOrdinaryClosedCompletion.lean:24` was reported. The owned modules have no new warnings. Earlier failure logs retain the missing-import/instance and reserved-keyword corrections.

`effects-public.lean` contains ten public axiom probes and ten signature probes. Its direct pinned Lean run exited 0 without warnings. Dependencies use only standard `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` dependency occurs.

`effects-kernels.lean` contains six direct integration theorem checks. Its run exited 0 without warnings. They compose the actual inherited prefix with one indexed descent; perform two sequential raw edge rebuilds without resetting warm tables; publish actual node and edge requests; and finish exact running node and edge owners with independently supplied proved local laws. The finish checks retain the exact returned cell and the full Post.

The general joint caller induction remains the parent task. These helpers provide its concrete constructor and allocation transitions. They do not prove whole-caller completion, recursive termination, or GHC forcing and concurrency behavior. No Haskell defect or implementation fix was established.
