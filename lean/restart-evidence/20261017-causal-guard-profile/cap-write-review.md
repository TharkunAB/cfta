# Same-cell guard-profile experiments

Reviewed: 2026-10-17 04:30 CEST.

No counterexample was found in this bounded investigation. The stronger equalities `profile P body = profile P ordinaryProbe` and `profile P body = profile P depthProbe` hold in every completed observation. The experiment tests actual source-created cells. It does not assume a desired stored body or construct an arbitrary cache payload.

## Completed checks

The final executable harness completed 19 targeted fixtures from empty source caches, followed by each fixture's immediate warm replay. These runs produce 50 retained-cell observations across 38 completed executions. The observations include 32 unused, nonhereditary finite positive-cap admissions. A cell retained in both phases is counted twice. The harness found zero implication failures at bounds 0 through 8, zero mismatches for either profile equality, and zero exhausted profile-checker traversals.

The fixtures cover raw and smart binder construction, nested binders with outer references, direct self-union cleanup, nonproductive Empty children, and opposite raw/smart first-writer orders. Only fixture indices 0–11, 18–19, and 24–28 are included in the completed total. The smart-outer nested batches 12–15 and 16–19 timed out at 20 seconds. Their partial or empty output is not a passing test and is not a counterexample. A later isolated 18–19 batch completed. The remaining fixtures were not run successfully.

`cap-write-experiments.lean` uses an executable Boolean-guard specialization of the frozen `GuardDepth` equations. Guards equal to `true` are allowed. It checks full structural traversal at fuel 128 for each observed body and probe. This checker is execution evidence. It is not a formal equivalence theorem for its implementation or a universal theorem about all source expressions.

`cap-write-nested-kernel.lean` supplies one independent formal integration result against the production observer. The closed expression is an outer raw binder with an inner raw binder and a constrained ordinary row that refers to the outer binding. The kernel constructs its own completed source execution from empty. It selects a literal populated Mu cell from the actual returned table, derives the semantic heap and body availability, and proves that the body and both probes have production profile `some 1`. All three have `Cap P 1`, while the body does not have `Cap P 0`; `usesLocal` is false. The same literal source expression then replays at the exact returned heap and retains the same root and entire heap. The public theorem has no supplied graph, cap, result, cache, or completion premise.

The final kernel check is `cap-write-nested-kernel-3.log`. It has one complete axiom/signature pair, no errors or warnings, and no `sorryAx`. The final harness logs each have two full axiom/signature pairs and no errors or warnings. `cap-write-validation.json` records each terminal status. Earlier failures, warnings, interruptions, and timeouts remain separate immutable artifacts.

## Causal proof boundary

These experiments and the kernel alone do not prove the universal stored-cell equality. A universal producer must retain a joint observation through the exact source callbacks and actual first-writer publication. The old depth observation determines literal Empty survival, root alternatives, direct references, and binder cleanup. The new guard-depth observation determines the guards and surviving nested Mu bodies. A scalar guard-depth equation alone does not justify the actual filtering and canonicalization steps.

A useful target is a causal heap invariant that gives both profile equalities for every populated Mu record. Its source-construction induction must establish the candidate law from the exact depth, ordinary, and fresh-body callbacks before `complete`. The old-record branch must retain the earlier law. Warm readback then uses `InternedProfileHeap.stored_probes` with actual probe availability and coherent facts to identify the complete stored probe records, not just their numeric identities. Exact equality implies the original positive-depth implication; it does not need the extra `usesLocal = false` condition.

`InternedFreshOrdinarySemanticOrigins.Origin` stores an actual historical `Context` and exact probe/body calls. That historical `Context` contains normalization, available inputs, decoded root profiles, and free-name profiles. It does not contain a guard-profile heap or a historical depth-heap premise. Current semantic facts cannot supply a missing historical invariant. The new joint invariant must be produced at actual writes, or carried by an appropriately strengthened source context. The existing `SemanticHeap` definition also has no guard-profile field.

The investigation concerns the current sequential Lean source constructor model. It establishes no Haskell runtime fault, GHC laziness claim, termination theorem, general recursive native cap closure, or whole-library completion claim. No Haskell or production Lean file changed in this task.
