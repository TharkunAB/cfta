# Target source and resource review

No material defect found. This review covers the final TargetResources source with SHA-256 `c7b7dcbbe53e45fb0b252ea5fb36552199a06d058b2375f2c6744b7d1d2f9ca8`. The final root-owned canonical log, `target-resources-build-4.log`, records 1343 successful jobs. This review ran no build and changed no production source.

## Target association and captured inputs

`cfta/src/Data/CFTA/Equality/Operations.hs:228–240` defines the target as `intersectList [mergeAlternatives (getPath other ns) | other <- Set.toAscList paths, other /= p]`. Its nonempty case is `foldr intersect seed rest`. The paths come from the original class in ascending order, with the selected path removed. All operands for one target use the same captured `ns`. The outer class fold can change the forest before the next class. It does not change the captured forest between operands of this target. `SourceEqualityClassTarget.operandPaths:20–22` uses the same exclusion and maps natural path components with `Int.ofNat`. This adapter does not claim arbitrary record lists are source-sorted.

For operand paths `[p0,p1,p2]`, the result expression is `operand p1 ∩ (operand p2 ∩ operand p0)`. The modeled serial schedule evaluates operands `p1`, `p2`, `p0`, then the two intersections from the inside out. `SourceCurrentAllocatedTargetGraph.Operand:35–42`, `Fold:110–119`, and `Target:121–127` retain this order. The literal worker follows it at `SourceCurrentAllocatedTargetWorker.lean:70–103`. Projection precedes Merge at the actual advanced checked state. Each later stage uses the returned checked state and warm merge memo. The empty target returns Empty with the whole initial state and memo.

## Projection and Merge branches

`Interned/Operations.hs:787–792,810–814` returns the selected forest member, or Empty if it is absent. An ordinary node projects each present child in row order and unions the results. The finite ordinary domain excludes the recursive, explicit-union, and unresolved-reference cases throughout the forest.

The Merge grouping key is symbol plus child count (`Interned/Operations.hs:627–630`). Groups of at most four rows retain each row's full guard. Larger groups merge corresponding columns and construct one unconstrained row (`:619–624,634`). A retained singleton column returns directly; other ordinary columns union and recurse (`:640–648`). The modeled branches use the same threshold and guards in `SourceCurrentAllocatedMergeGraph.lean:41–78`. Its large-row instruction also records canonical empty equality-field allocation (`:138–140`). This separate equality allocation is outside the node/edge constructor-request counts.

## Initial-only resource recurrence

`TargetBudgetNumbers.lean:29–54` first bounds each original operand by `Q = envelope (forestRows R C D) H`. For `k` additional operands after the seed, the row recurrence starts at `T0 = Q` and squares `max Q Tk` at each native query. Both supply recurrences charge the head operand, the shorter tail, then the native budget at their common profile. They use arity `max A 1` to include returned sentinels. Height stays at most `H`. Thus there are `k+1` operand calls and `k` native queries. The edge recurrence conservatively uses the same native Work bound as the node recurrence.

`TargetResources.fold_complete:97–178` constructs the head, recursively constructs the tail at its exact returned state, and then constructs the query there. It derives intermediate readiness, availability, profiles, stores, and query word checks. It concatenates the actual request traces in that same order. No current-query success, completed Target, intermediate count, or future range plan is an input. The whole-target wrapper at `:181–245` gives zero requests and zero rows to the empty case. Its nonempty case uses the fold theorem and derives stable literal-worker completion. Initial headroom, resident forest profile/height/path limits, semantic inventory admission, and valid warm cache certificates remain explicit.

## Correspondence boundary

This proves a completed sequential Lean execution and constructor-request bounds. It does not prove the Haskell demand schedule, CAF forcing, early memo publication, pending ancestors, or concurrency (`SourceCurrentMemoMergeGraph.lean:10–13`; `SourceCurrentAllocatedTargetComplete.lean:7–10`). Haskell uses `HashMap.elems`; the model fixes a bucket order. `MergedSourceGrouping.groups_correct:51` and `grouping_permutation:59` state the partition and bucket-permutation contract. They do not identify a concrete host hash-table enumeration or the resulting physical identity and cache-hit history.

Merge is an over-approximation in the source (`Interned/Operations.hs:588–609`). The target receipt supplies the existing selected-subterm inclusion law. It does not make Merge an exact language transformation. Native intersection has its own exact operand-language law. These results do not establish whole constrained reduction, general recursive completion, all Sized API laws, or whole-library Haskell correspondence. No Haskell defect was identified.
