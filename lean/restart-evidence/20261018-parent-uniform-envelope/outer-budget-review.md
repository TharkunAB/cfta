# Actual outer Parent call budget

Reviewed on 2026-10-18 at 06:20 CEST. Production SHA256: `c04d2cd242b6e8a045576bbfa17cc3c83358edc4e48f826274380c4447d4f8a5`.

## Exact execution scope

`SourceCurrentOuterCallBudget` replays all eight literal outer phases from `SourceCurrentAllocatedPartialWorker`. `Execution` retains the full successful or failed outcome and an ordered list of Parent invocation entries. Each entry contains the complete stored `EdgeRequest` and the full caller immediately before the Parent body. Edge demand selects the actual stored owner. A ready hit contributes no entry. The edge body contributes one entry even if Parent fails.

Replay bind inspects only the actual first outcome. It enters the continuation only after success and appends that continuation's entries. A failed outcome retains the preceding entry list and skips every suffix. Thus the list does not enumerate unexecuted requests. The proof establishes equality with the original full worker outcome, including its returned or failed caller. It changes no worker definition and makes no host evaluation or scheduling claim.

The public `node_budget` and `edge_budget` endpoints require only the inputs of the corresponding literal workers. They have no successful completion, Ready, semantic domain, reached range, source height, Cap, or recursive callback premise. Private simultaneous induction proves outcome equality and the count bound for node call, node body, edge call, edge body, rows, descendants, children, and walk. The finite same-fuel phase chain contributes no extra Parent sites. Rows has three smaller calls; walk has two. These facts justify `budget 0 = 1` and `budget (fuel+1) = 3 * budget fuel + 1`.

This is a conservative bound on entered Parent invocations. It does not count Mu reconstruction, raw rebuild, inherited descent, native instructions inside Parent, or other allocations. It does not prove outer completion or a complete outer heap resource budget. The entry list comes from the exact replay definition. This component does not export a separate Reached, per-site semantic availability, or global resource transport theorem.

## Constructed integration

`MicroCFTA.OuterBudgetKernels.ordered_sites_and_stopping_prefix` builds a two-row source node from empty constructor storage. Both raw guards are contradictory. It starts empty outer result tables and uses no lower worker fuel. The outer fuel-three call enters the two Parent rejection sites in order, with literal symbols `first` and `second`, and returns successfully. The outer fuel-two call stops with `exhausted rows` after exactly one entered Parent site. The omitted suffix contributes no entry. An all-zero-fuel node call from the returned caller is a warm hit with the same full result and caller and no Parent entries.

The witness invokes the public fuel-only theorem for the full and truncated calls. It supplies no future graph or returned-state bound. It establishes an actual constructor source and literal bounded executions. It does not assert semantic Ready or a live native query for this rejection fixture. The generic theorem covers all live, failed, and warm cases independently of that fixture.

## Checks and preserved attempts

- Selected source check: `outer-budget-direct-4`, exit 0, log size 0 bytes.
- Canonical check: `outer-budget-canonical-1`, exit 0, 1,413 jobs. It replays only the unchanged `InternedFreshOrdinaryClosedCompletion` warning.
- Imported public group: `outer-budget-public-1`, nine full signature/proof/axiom pairs. It covers Execution, its constructor and two projections, budget, node, edge, node_budget, and edge_budget.
- Selected constructed check: `outer-budget-kernels-2`, exit 0, log size 0 bytes.
- Constructed group: `outer-budget-kernels-public-1`, one full signature/proof/axiom pair.

Every selected source has all eight required printer/linter options. Each group uses `#check @`, `#print`, and `#print axioms`. Logs contain no printer omissions or errors, and axiom reports contain only propext, Classical.choice, and Quot.sound. Proof aliases retain exact checked private witnesses.

All source checks execute immutable numbered snapshots with pinned Lean 4.34.1 and `-Dlinter.all=true`. The worker records effective MemoryMax and MemoryHigh of 4,294,967,296 bytes, SwapMax 0, and a five-minute cap. The selected source, canonical, public, constructed source, and constructed printer peaks are 197, 269, 122, 196, and 208 MiB.

Source attempts 1 and 2 remain preserved with their raw errors. They failed on unused instance scope, the Nat inequality lemma name, and elaboration of paired matches. Source attempt 3 succeeds and remains preserved; attempt 4 adds only the explicit non-Parent allocation boundary to the header. Constructed attempt 1 failed because `simp_all only` made no progress in an impossible-case split. Attempt 2 proves the exact failure-state equation directly and succeeds. No source behavior or theorem domain changed to resolve these failures.
