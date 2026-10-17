# Independent actual allocation trace review

Result: no material defect found in `SourceCurrentAllocatedRecursiveAllocationTrace.lean`, SHA-256 `b0b59fc522d1eff38b0a0761a9b112d3a7c4bbd4d63014017e39734326dd4c63`.

## Actual instruction accounting

`stepCharges` (lines 35–43) charges literal Work by the observed request list at its actual entry heap. It charges an optional binder by the full budget of the syntax encoded from that instruction's current immutable body. All other instructions have zero constructor allocation charge. Node and edge counts remain separate.

`chargesThrough` (46–54) follows the actual checked step. It adds continuation charges at the yielded control and complete returned state. It stops at every non-yielding outcome. It does not replace an actual recursive branch with a requested result or assume future success.

`step_bound` (57–93) covers every stopping outcome. Work uses actual reservation accounting. Optional-binder accounting uses the all-outcome syntax bound and the current input availability. The current edge body allocates equality fields but leaves the native constructor heap unchanged. Its constructor charge is correctly zero. Node and edge demand can change memo tables but do not allocate constructor identities at that step. Enter changes domains, read loads a value, and finish publishes a result. Zero constructor charges do not mean these instructions leave all state fields unchanged.

`prefix_bound` (96–115) inducts on the supplied actual physical Trace. Each instruction carries its current input check. Existing physical preservation derives Good and continuation fields at that exact return before the smaller trace is used. The proof adds the actual local charge to the suffix bound. It returns final validity and fields without a future readiness or result-count premise.

`charges_append` (118–128) needs literal raw Steps for the first segment. It evaluates the suffix at the exact common control and checked state. It does not evaluate that suffix at a reconstructed heap or the original heap.

## Imported checks and constructed integration

Root strict direct attempt 3 has an empty log and matches the reviewed source. Canonical build `canonical-allocation-trace-1.log` completes 1091 jobs with exit code 0. It replays one old unused-input warning from `InternedFreshOrdinaryClosedCompletion.lean:24`. It emits no new-module warning. All five public APIs have full explicit signature and axiom probes. The public log has five clean pairs. The final integration log has two clean pairs. Neither final imported log contains errors, warnings, or `sorryAx`. Only standard Lean axioms occur.

`used_optional_work` starts from legitimate initial Good, an available body with a used literal intersection pair, and an initially allocated guard field. It constructs its own actual optional-binder completion from the initial Context, decoded depth heap, and coverage in Good. It supplies no completed binder or future heap. Its body can contain open nested Mu values. It has no PreparedWithoutMu, hereditary annotation, cap, or ordinary-only premise.

It then constructs the literal checked optional-binder step followed by `makeEdge symbol guard [value]` in that binder's actual returned heap. The produced value availability supplies the raw edge's physical input. The kernel constructs a two-step physical Trace and derives final Good. The node counter is bounded by its initial value plus the optional syntax budget. The edge counter is bounded by its initial value plus the optional budget plus one. It proves literal retention of native node and edge tables, domain cache, and equality operations.

`used_optional_charges_append` constructs that same prefix from the same initial facts. It forms the first raw one-step prefix from the actual optional-binder yield. It then instantiates charges_append at that exact returned state and raw edge continuation. It retains the constructed full Trace and final Good. Neither kernel receives a successful execution, later-entry resources, a future WordRanges proof, or a count oracle.

The first independent kernel attempt used the reserved keyword `prefix` as a local name and contained one unused simp argument. Its source and raw diagnostic log remain preserved. Attempt 2 fixes those elaboration details and is the final clean probe. All three root production attempts remain preserved. This independent review changed no production source.

## Scope

The production result verifies supplied actual prefixes. The integration independently constructs a local prefix from initial facts. The charge depends on the executed prefix and reached optional-binder bodies. It is not a bound computed solely from the original root query.

A complete initial generated-query estimate must still bound total observed Work and every reached encoded optional body from the original input profiles and query structure. These counter inequalities do not bound heap payload size, equality allocation, domain allocation, total host evaluation, arbitrary interleavings, or cumulative result-fed queries.
