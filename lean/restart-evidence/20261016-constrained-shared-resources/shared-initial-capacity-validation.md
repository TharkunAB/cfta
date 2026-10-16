# Initial shared capacity validation

Date: 2026-10-16 21:07 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinarySharedInitialCapacity.lean`.
The frozen source has 103 lines and SHA256 `7afc47cb68031e323c7b8e4405285cfc7d903710bc3c51e5ba1b5679e5ce1648`.
The evidence copy is byte-identical.

## Checks

- Direct source check 2: terminal exit 0, no diagnostics.
- Parent confirmed canonical terminal exit 0, 1360 jobs, in `shared-leaf-capacity-build-2.log`. This batch builds SharedInitialCapacity and the separately owned SharedLeafResources. Only the historical unused-input dependency warning remains.
- Final canonical imported public check 2: terminal exit 0, 3 public axiom probes and 3 full signature probes.
- Final canonical imported integration check 2: terminal exit 0, 3 kernels with an axiom and signature probe each.
- Final direct and imported logs contain no errors, warnings, or `sorryAx`. All reported axioms are subsets of `propext`, `Classical.choice`, and `Quot.sound`.

Direct source check 1 needed fully qualified budget definition names in two simplifier arguments. Source check 2 passed after those local proof corrections. Integration check 1 needed explicit section-variable inclusion. Integration check 2 fixed only the evidence file and passed against the canonical source. Earlier draft logs remain intact. Public check 1 used the same direct source through a temporary import directory. Public check 2 used the canonical import.

## Produced plans

`force_unique` compares two actual raw Force graphs through their constructive stable literal-worker executions. It chooses the maximum of each of five stage bounds and uses constructor injectivity at the same literal call. It proves equality of the returned value and the entire shared state. This includes the checked native state, equality operations, slots, and Merge memo. It takes no readiness, semantic, result, or range assumption.

`force_capacity` derives the old ForceCapacity predicate from the original resident captured forest, coherent selected class membership, profiles, height and path-depth bounds, valid warm cache certificates, and slot-sensitive initial headroom. A missing slot uses exact operand count `record.paths.length - 1` and TargetInitialCapacity.target_capacity. A present slot makes the old miss-only capacity obligation vacuous. No completed Force or reached capacity is an input. An active-class premise is not needed for this endpoint.

`leaf_capacity` uses the same original data and the active-class premise required by ForceResources.complete. It constructs an actual force receipt from initial headroom. For each raw Force in the old universal leaf plan, force_unique identifies its complete returned shared state with that constructed receipt. The returned Capacity then transfers to the exact raw prefix. The input value is arbitrary because this numeric plan does not yet check its residency or domain.

## Integration

1. Any raw Force from a present slot returns its exact cached value and whole initial shared state. The check compares it with the actual hit constructor.
2. Initial force resources plus a resident finite-ordinary input derive both existing ForceRanges and LeafRanges. The check supplies no old numeric plan and no future readiness or capacity.
3. The same initial facts construct an actual leaf receipt, stable literal leaf execution at the same whole returned shared state, structural stores, and the input-to-result NodeNarrow law. The initial capacity plan is derived internally.

LeafCapacity requires layout capacity after the earlier force and before the current native query. This module does not reserve that query's constructor requests or assert final leaf capacity. SharedLeafResources supplies that separate cumulative accounting. The general class, outer cumulative budget, and Haskell host-demand correspondence remain separate.

No older source, Haskell, Audit, root document, or earlier evidence was edited. This owner ran no Git or Lake command. New source and owned text have one final newline and no blank line at EOF. Compiled objects remain outside the evidence directory.
