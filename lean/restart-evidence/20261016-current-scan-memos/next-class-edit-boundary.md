# Next checked class-edit boundary

Read-only source audit, 2026-10-16 08:25 CEST. No proof or Haskell edit and no build ran.

## Current established entry

`SourceCurrentConjunctionAllocatedRequired.finite` (`lean/MicroCFTA/SourceCurrentConjunctionAllocatedRequired.lean:39`) constructs the actual allocated precheck, current Scan, and successful required-path continuation. Its successful branch retains actual records, order and coherence, current checked state, live equality operations, concrete inventory At, the three global receipts and fourth Correct (`:67-77`). The required receipt preserves the exact native tables/domains and operations, derives available results and every selected `ForestClosed` path, and states the exact required-language restriction (`SourceCurrentConjunctionRequired.lean:106-127`). It does not complete class edits or the outer caller.

## Why the old pass is not a checked-state continuation

The old `SourceCurrentMemoClassPass.Class/Fold/Pass` runs over `SourceRecursiveIntersectionThunks.State` plus a merge Memo (`SourceCurrentMemoClassPass.lean:26-51`). Its shared state has only `native`, `targets`, and `memo` (`SourceCurrentMemoSharedTargetState.lean:26-42`). It has no equality-operation state.

Both target combination (`SourceCurrentMemoDemandTarget.lean:33-36`) and leaf narrowing (`SourceCurrentMemoSharedTargetLeaf.lean:26-28`) invoke `SourceEqualityNativeScoped.Step`. That Step is indexed by actual **older** `SourceRecursiveIntersectionNative.execute`, with its old WordRanges (`SourceEqualityNativeScoped.lean:41-50`). Its IdleReady contains the old `Thunks.Valid` over `NodeGood` and `EdgeGood` (`:19-23`). The current entry instead has checked NativeDemand execution, physical cache validity, same-cache Fields, Contextual, Covered, syntactic scope, and retained equality operations. Erasing operations is not a theorem that these execution graphs or their warm cache laws coincide. Closed operands alone do not justify this substitution.

The old end-to-end `source_cold` is useful component evidence but has exactly those old state and execution premises (`SourceCurrentMemoClassPassComplete.lean:31-54`). Its language theorem gives unconditional narrowing and conditional equality under the retained classes (`SourceCurrentMemoClassPassLanguage.lean:127-138`), not a current checked caller theorem.

## Source schedule and optimizations to preserve

- `Equality/Operations.hs:207-226`: preserve the empty/empty fast path, contradiction shortcut, ordered refused/retained partition, stopped refused-class shortcut, and one requireAll before class editing. The live-class proof must not be advertised as the whole caller before the other branches are connected.
- `:211`, `:236-244`: process retained classes by a right fold. Each class captures the forest returned by its tail. Build edits in ascending path order. For path p, capture all other paths in ascending order and exclude p. Do not let edits earlier within that class alter its captured original forest.
- `:228-230`: the target list is first-seeded. For operands A,B,C the actual right fold combines B with (C with A); the empty target is EmptyNode. Project/merge each demanded target operand before the recursive suffix and its final checked intersection.
- `:310-334`: retain the compiled edit trie, child-list root no-op, empty-node shortcut, Mu/union head exposure, original row guards, and actual signed-map edit behavior. Unselected siblings can stay open. The source Rec error is unreachable only after the selected-path safety proof, not by a global closure assumption.
- `:203-204`, `:211`: run final empty propagation once after all classes. A single reduction pass does not itself iterate to a fixpoint (`:175-180`).
- `Interned/Operations.hs:611-648`: retain actual completed merge memo hits; closed ordinary roots only; grouping by symbol and arity; at most four rows unchanged except recursive child merges; larger groups create one unconstrained row; retained-column deduplication; recursive-boundary union; and structural subsumption filtering. Merge is an over-approximation (`:588-609`). The original class constraints must remain checked.

These are completed sequential graph requirements. HashMap iteration, lazy forcing, and actual pending memo publication remain runtime adapter boundaries.

## Smallest honest next component

Start with a **checked, allocation-aware merge and target operand**. Do not port the whole class pass by coercing its state.

1. Lift actual merge calls through a checked state, retaining the live equality operations and all warm native cells. The existing heap-only `SourceCurrentMemoMergeGraph.Call` and constructive completion can supply the heap/merge-table component, but a completed Call by itself does not prove checked Good or same-cache Fields. Native wrapper `Merge.done` advances only a heap (`SourceCurrentMemoMergeNative.lean:23-28`).
2. Prove same-cache Fields through that exact merge schedule. `SourceCurrentMemoMergeFieldHeap.call_heap` (`:150-157`) already preserves an arbitrary annotation, so specialize to `FieldAvailable operations`. Its **explicit** Top annotation premise must be discharged in the actual cache. Large groups can introduce Top even when it did not occur among the input guards. `SourceCurrentConjunctionFieldAllocation.empty_field` (`:83-93`) derives Top availability after the literal emptyField allocation. Existing actual load/constructor receipts can also establish an already-present Top. A source-faithful adapter must place an allocation only where that actual constructor/accessor is demanded. Do not prewarm on a memo hit or small branch. If only an initial Top-available component lemma is proved first, state it as an initial condition and do not claim the current caller discharges it yet. Normalized raw Top alone is insufficient: `ConstraintFieldLookup.load` can return `.ok none` for an absent live key (`SourceEqualityConstraintFieldLookup.lean:18-23,30-35`).
3. Define an operand as the literal selected Forest projection, then that checked merge. Projection preserves operations and all native tables; `ProjectionPathDomain.forest_effects`, `ProjectionCosts.forest_effects`, and annotation projection derive its facts from Values plus the selected ForestClosed domain. There is no need for ClosedValues of the captured forest.
4. Return a new checked operand receipt with Ready/Good, same-cache Fields, costs, actual operation growth, Extension, closed available result, merge Stored and CacheCovers, retained merge entries, unchanged native tables where true, At transported through heap-only advancement, and exact projection-plus-merge global receipts. Construct its completion from the current initial invariants; do not take a supplied completed merge or desired result law as the outer public completion premise.

The existing merge layer is reusable, not an unsolved algorithm: `MemoMergeComplete.finite`, `MemoMergeEffects.Stored.grows`, `MemoMergeLanguage.call_language`, and `MemoMergeQueryMemos.call_memos` (`:186-197`) already construct or verify actual heap-only calls. What is missing is their actual equality-allocation and checked-state lift. Warm merge tables require causal Stored and language coverage (or an actual history deriving them); empty tables derive these vacuously. Preserve an existing warm table across classes. Do not silently reset it.

## Then the checked target, force, leaf, and class fold

A new shared state should contain the **full checked native state**, class-local target slots, and the actual completed merge Memo. Keep the separate three global and fourth emptiness tables indexed through the actual graphs. At the start of each class, clear only class-local slots. Native request tables, domains, operations, merge Memo, and global tables remain warm.

For target-fold and leaf intersections, use `InventoryState.query_complete` (`:85-108`), not the old Scoped.Step. It derives actual checked execution, exact physical intersection language, closedness, syntactic scope, final Contextual/Covered, and a computed next inventory from closed resident generated operands and reached checked WordRanges. A generated merged target does not need supplied model validity. Required path domains and edit safety derive the leaf input's closedness; no whole-forest closure is needed. Use `AllocatedNativeTraceEffects.effects` (`:30-57`) for physical effects and operation growth and `AllocatedNativeGlobalMemos.trace_memos` (`:85-97`) for the same actual trace's silent global-unfold receipt and final table coherence.

A stored target slot must retain a historical **new checked Target** receipt, its actual captured forest, closed available result, and heap retention. A slot hit performs no target recomputation and supplies no fabricated calls. It need not put the slot result into the old model: the next generated query derives that admission when it is actually requested.

Port the structural domain and edit-trie proofs to the new leaf contract. Reuse `CurrentEditDomains.Transport`, the existing compiled-path/disjointness lemmas, the ordinary row constructor and recursive Head effects, and arbitrary-query ForestClosed transport. These proofs must derive each head class's domains from the actual completed tail. The old graph's structure is a precise blueprint (`SourceCurrentMemoSharedEditGraph.lean:21-73`); its leaf execution is not interchangeable.

The new finite class/fold endpoint should require only initial selected path domains and range plans at actual reached checked requests. It must derive intermediate availability, Fields, inventory At, cache coverage, and language bounds. No whole completed-class callback, future Ready/Fields, parent language oracle, or future successful target can be a completion premise.

## Remaining outer-caller obligations

After the checked class pass, compose the same actual precheck/Scan/required result and the same retained records with this new right-fold pass. Derive unconditional forest narrowing, conditional preservation under each actual retained ClassSat, and final empty propagation. Then relate original physical edge constraints and inherited constraints to those class conditions before claiming parent-edge language preservation. Do not drop the retained equality checks merely because target merging over-approximates. The ordinary outer reduction traversal, recursive binding/caller memo protocol, and runtime publication remain separate until their actual source graphs are connected.

## Snapshot hashes

- `cfta/src/Data/CFTA/Equality/Operations.hs`: `5bf6e9b0f4033c11ac7723a17fe8d1b94d95a259187f0402285ad0147e439b09`.
- `cfta/src/Data/CFTA/Interned/Operations.hs`: `edea6782e2f88aebbe26de290f2eb581c3557747760dfae19b5d1cbe49a17b4c`.
- `lean/MicroCFTA/SourceCurrentConjunctionAllocatedRequired.lean`: `3888e7d3187d2343af627c24a6d4faf8edd004cef0618b9f32e07f6eccc71175`.
- `lean/MicroCFTA/SourceCurrentConjunctionRequired.lean`: `ebcb0053a8760f6a1c831d8d89253c2dc1243f25fac8ba06a646dd3a42d9359e`.
- `lean/MicroCFTA/SourceCurrentMemoClassPass.lean`: `a7d75508c47f773db865d8bea400ac046a2777739356f2a700ef6205c6b8227d`.
- `lean/MicroCFTA/SourceCurrentMemoDemandTarget.lean`: `d5eab06dd51f02de45cd1be2ddd67a1adff6ce9b39cc62b3926aec4c8efe7e1d`.
- `lean/MicroCFTA/SourceCurrentMemoSharedTargetState.lean`: `32b16925351ad0647fdc608c540c7a5ecfffa5c3753d04cb1d5f8430384c4e56`.
- `lean/MicroCFTA/SourceCurrentMemoSharedTargetLeaf.lean`: `9222020c73239898b1e6aba567b9ca8f97d86b200e9505c1e868e66ad9311334`.
- `lean/MicroCFTA/SourceCurrentMemoMergeFieldHeap.lean`: `d4f14118dc5e1bbdc820d367b7ee62b66615126c5abddcdc2e36fab40ac8a8ac`.
- `lean/MicroCFTA/SourceEqualityNativeScoped.lean`: `572d68d46d10fa921bd49b084d69882d746f617e54c3f443907ce8a989292997`.
