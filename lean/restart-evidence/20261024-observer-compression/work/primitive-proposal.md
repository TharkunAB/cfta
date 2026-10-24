# Paired primitive reads through a compression frame

Source-only proposal, 2026-10-24 02:09 CEST. No blocker was found for this route. No body was authored and no compiler or prepared program was run. The reviewer did not author the installed frame or primitive read implementations.

The minimum addition is `Frame.symm`, two paired-read comparisons, and two finite-read transports. Use the existing `Frame`, `Success`, `Reaches`, and read actions. No new relation, state machine, semantic predicate, `Safe`, `Ready`, or desired-output premise is needed.

The proposed interfaces are:

1. `Frame left right → Frame right left`. Reverse each of the five nonforest field equalities and each root/size-path equivalence. This result needs no totality premise.
2. Given `Frame left right`, `Total left.representatives`, and actual successes of `representative leftFuel uv` and `representative rightFuel uv` from the respective inputs, return equality of their root IDs and `Frame leftAfter rightAfter`.
3. Under the same input frame and left totality, actual successes of `getValue leftFuel uv` and `getValue rightFuel uv` return equal `UVarValue Symbol` values and `Frame leftAfter rightAfter`.
4. Given the input frame, left totality, and one actual successful left representative read returning `root`, produce `∃ rightFuel rightAfter, Success (representative rightFuel uv) right root rightAfter ∧ Frame leftAfter rightAfter`.
5. Given the same frame and totality and one actual successful left value read returning `value`, produce `∃ rightFuel rightAfter, Success (getValue rightFuel uv) right value rightAfter ∧ Frame leftAfter rightAfter`.

All fuel arguments are independent. These interfaces make no equal-fuel assertion across distinct forests. Applying the transport result to the symmetric frame gives the reverse direction. Right totality is derived once as `inputFrame.total leftTotal`; it is not another caller premise.

For the paired representative result, extract the two actual lookup witnesses with `representative_success`. `findRoot_correct` gives their paths in the two input forests. A left path moves to the right forest with `(inputFrame.reaches uv root size).mpr`. Apply `reaches_unique` against the actual right path to identify the returned roots. The existing `representative_frame` supplies both read frames. The final frame is exactly `leftReadFrame.symm.trans (inputFrame.trans rightReadFrame)`.

For the paired value result, the existing `getValue_frame` already supplies each read frame, actual root/size paths, and the exact input slot read. Use the same path uniqueness argument for the two roots. `inputFrame.values : right.values = left.values` then puts both stored reads at the same slot in one array. `Option.some.inj` gives equality of the returned values. No `DecidableEq Symbol` or payload-coherence premise is required.

Finite transport must be exported, rather than leaving the comparison conditional on both reads already succeeding. For representative transport, either reuse `EnumerationExecution.representative_terminates` on the derived right totality and then apply the paired comparison, or construct the witness directly from the transported left path with `findRoot_terminates`. The existing termination theorem is the smallest reuse. Its output root need not be assumed equal; the comparison derives equality.

For value transport, extract the actual left lookup and stored slot using `getValue_success`. Transfer its path to the right input and apply `findRoot_terminates`. Path uniqueness identifies the newly found right root with the observed left root. Transfer the stored slot using `inputFrame.values`. Define `rightAfter` as the exact record update `{right with representatives := rightFound.forest}`. `getValue_success.mpr` constructs the actual successful right read. Apply the paired result for its final frame. This construction returns the same complete payload and preserves all ancestry and obligation fields through the frame.

Totality alone does not imply a successful value read. A total empty/default forest with `values = []` has a representative for every variable but no readable slot. The supplied successful left read is therefore substantive: it provides the slot needed on the right. No separate final-slot or desired-value assumption is required.

Existing APIs avoid duplicate work:

- `EnumerationCompressionFrame.lean:20–86` defines the complete frame, reflexivity/transitivity, totality transport, and the two single-read frames. Symmetry and paired comparison/finite transport are not present.
- `EnumerationSchedule.lean:54–75` exposes exact representative lookup and its complete forest update. `EnumerationCorrectness.lean:1018–1034` exposes the exact value-read slot and update.
- `EnumerationExecution.lean:99–111` preserves successful reads at larger fuel. Lines 413–419 construct a finite actual representative action from totality. Reuse these facts rather than proving another termination worker.
- `UnionFind.lean:52–65`, 160–177 supplies path uniqueness and finite lookup witnesses. The witness returned by `findRoot_terminates` has no endpoint equality in its statement; obtain that equality with `findRoot_correct` and `reaches_unique`.
- `EnumerationDriver.lean:218–240`, 398–428, and 664–696 supplies known-root/ready and storage reads. These require `Safe`, allocation bounds, known roots, or `Ready`; they do not provide the desired weaker paired interface. There is no separate `EnumerationDriverReadability.lean` file in this tree.
- `EnumerationRendering.lean:35–61` supplies a finite enumerated-value read only for completed graph-bearing classes under `CompleteGraph`, `Safe`, `Finished`, and `CarriesGraph`. It should remain a consumer of the weaker primitive result, not a premise of it.
- `EnumerationUntilBridge.lean:77–99` proves equal values for two consecutive successful reads at the same variable. It has no frame input, no independent related input state, no final frame, and no constructed second read. Retain that theorem and avoid reproving its special sequential result.

These results cover the two modeled primitive observers and their finite successful executions. They do not show that arbitrary callbacks agree. A callback can inspect the raw representative forest and distinguish framed inputs. A shared-driver bridge must separately establish congruence for its actual observers and thread the resulting frames through callback and recursion ancestry. The complete frame already preserves both ancestry fields; `RenderStable` does not.

Exact source identities read at this cut:

| Source | SHA256 |
| --- | --- |
| `EnumerationCompressionFrame.lean` | `5b6e6a4b11c21b949874db500e23aa074fcdd4e0de683f46f33863113dc91375` |
| `EnumerationSchedule.lean` | `3e84f2059725b3c0392d4df005574fde2918290cb393c4be0d549a62ad4a4e45` |
| `EnumerationCorrectness.lean` | `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d` |
| `EnumerationExecution.lean` | `b81e03600e03085ec32fc8c85026ca4af562593764b28d6f8dd776eb3ac98346` |
| `EnumerationDriver.lean` | `0769d78e4d3c01d959cf21c5a59642fee164dc60655e86601458a799da72bbcf` |
| `EnumerationRendering.lean` | `be611f9aa9e285872251ad14a40126fa358f393520f14576c9770ffa959db1a9` |
| `EnumerationUntilBridge.lean` | `ac5eb73483f5d59bf52f1a251c55322050f289cc8a9dd052d032ab8e32638642` |
| `UnionFind.lean` | `3668867a41890e4721c301092a06c48d3bd757a8eede4b92340fe5db80119a14` |
| `EnumerationState.lean` | `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4` |

Read scope: the whole 145-line compression-frame source; the exact live cuts listed above; `EnumerationState.lean:105–136`; and targeted searches for existing paired, termination, and readability results. This report does not claim a fresh manual read of the complete execution, driver, rendering, or import-closure sources.
