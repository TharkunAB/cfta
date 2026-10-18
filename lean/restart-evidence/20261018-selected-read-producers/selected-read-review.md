# Actual target writers and semantic read producers

Reviewed on 2026-10-18 at 05:26 CEST. All three new source modules and their final strict/canonical/public receipts are reviewed. Final component pins accompany this report. No production source changes or new Lean builds were made by this independent review.

## Precise next result

A target-slot writer must identify the actual historical target worker, its captured forest, its operand paths, its complete entry/return states, and the absent-before-store branch. This is useful causal information. It does not by itself yield the existing semantic `SlotReceipt`.

The next semantic composition point is exact:

```
actual target return at the recovered writer entry
+ semantic Frame/admission at that entry
+ selected ForestClosed domains for that captured forest
+ Stored and CacheCovers for its entry Merge memo
+ valid entry global memo bundle
+ initial numeric reservation, or the reached checked-Trace obligations
=> TargetReads + TargetComplete.Receipt at those same literal endpoints
=> semantic SlotReceipt retained into the leaf's actual reader
```

The writer entry is historical. Current heap growth does not prove that historical entry's semantic cache admission or global memo validity. These facts must be transported forward from a legitimate initial context along the actual prefix. They must not be assumed from the final target value.

## Existing producers that already discharge the bounded case

`SourceCurrentTargetNumeric.complete` is an initial-only producer. It takes Frame/Fits, selected domains, physical Stored, language CacheCovers, valid globals, and the pure initial TargetReserved predicate. It constructs its own Target graph, TargetReads, semantic receipt, returned Frame/Fits, and exact common-fuel worker return. There is no input cap or whole-forest closure premise.

`SourceCurrentAllocatedTargetWorkerCompletion.target_done_unique` compares any two successful target fuel tuples from the same complete initial state. It identifies the result, returned checked state, and Merge memo. Thus a supplied actual return can be aligned to the result constructed by TargetNumeric.complete. The supplied fuel need not be at least the forecast fuel. This is a short alignment composition, not a new termination argument.

`SourceCurrentClassNumeric.complete` and `SourceCurrentClassPassNumeric.fold` already do the same at class and right-fold scope. They construct ClassReads/FoldReads from initial class/fold reservations. `runClass_done_unique` and `fold_done_unique` align them with arbitrary successful literal worker equations. The full right-fold producer retains selected path support through each actual tail result and obtains the head's Room from the original pure forecast. It does not inspect a future completed forest to choose a bound.

Therefore the bounded semantic target/class producer is already present. A new module should not reprove it under another name. The remaining new task is to connect the actual-prefix causal writer interface to this exact initial context, or to supply the checked physical Trace at each actual query without a future range callback.

## Raw events, checked traces, and semantic receipts differ

`SourceCurrentActualSharedLeafEvents.target_leaf` derives the literal target force, checked request equation, and finite `SourceEqualityNativeDemand.Steps`. `Steps` records actual execution. It does not include the physical `Inputs` proof in each constructor.

`SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace` records those Inputs at every actual instruction. A successful interpreter return alone does not establish that the packed request keys satisfy the physical input checks. The current native interpreter does not turn all these proof obligations into runtime checks. Initial capacity or actual-prefix checked input producers remain necessary.

`SourceCurrentAllocatedTargetWorkerNative.of_done` currently constructs a Trace independently from physical Ready, idle native cells, resident closed operands, and WordRanges. Successful-return uniqueness aligns its exact final state with the supplied return. This is the old range-dependent point that a new initial capacity producer can replace. Projection and Merge already have direct worker-to-graph soundness; native request checking is the distinct step.

A checked Trace is still not the whole semantic query receipt. Exact intersection language and warm cache admission use the inventory's `At` law. `Frame` also includes the semantic/causal guard context, conditional joint cache laws, and captured source origins. Weak `SharedGood` does not include these semantic cache laws.

In particular, empty target slots do not imply empty or semantically valid native tables. A new class clears only its local target slots. Its native node/edge tables and Merge memo remain warm. The new literal writer theorem must preserve this support rather than silently requiring every table to be empty.

## New initial key admission and the exact invariant gap

`SourceCurrentNativeKeyAdmission` is pinned at SHA `fbc4ff1e912db248097e2e1374aa52eeb9279d65a10529ff62302863463ab25e`. Its `node_prefix` accepts actual raw Steps from a closed empty-domain request. Initial node/edge counter bounds and domain headroom construct its physical Trace. `node_done` extracts the raw prefix from a literal done result and derives checked Trace, availability, and numeric store/counter bounds. Neither theorem assumes future WordRanges, future result properties, or successful execution at some larger supplied fuel. The actual successful equation remains an observation to verify.

Its initial Good is `SourceCurrentAllocatedNativePhysicalCompletion.Good`. In particular, `SourceCurrentAllocatedNativePhysicalCache.Valid` checks `FlatMemoThunk.Valid (NodeKey width)` and `(EdgeKeyOf width)`. Those key predicates link each physical key to its captured request and include key safety.

The lower range-free worker invariant is different. `SourceCurrentNativeOperationHeap.Good` uses `SourceCurrentNativeOperationInvariants.Cells`, whose two table key predicates are `fun _ _ => True`. `SharedGood` adds physical Merge storage and resident target slots. Current capacity bounds do not recover the key-to-owner linkage of an arbitrary prepopulated weak table. An available returned value also does not imply its desired intersection language.

The next actual execution invariant must therefore retain strong native keys and semantic cache admission from a legitimate initial native state through the actual earlier queries. The new initial admission theorem supplies each checked query transition after these initial facts are established. Empty local target slots cannot discharge them. This is the concrete gap in a proposed weak-Good-only promotion to semantic SlotReceipt.

## Existing semantic slot contract

`SourceCurrentAllocatedSharedTargetState.SlotReceipt` contains all of:

- a class-path membership witness;
- actual historical before/after Checked states and initial/saved Merge memos;
- an actual Target graph over `operandPaths record.paths path` and the same captured forest;
- TargetReads for that graph;
- the complete TargetComplete.Receipt at a concrete historical inventory;
- Keeps into the current heap and Merge Extends into the current memo.

Its semantic inclusion is one-way common-subterm preservation. The target can have more language than the exact intersection of source selected values. `SlotReceipt.available` derives current availability and closedness. These facts do not follow from merely finding an available value in a weak physical slot table.

On a hit, `Force.Reads.hit` performs no target reads. Its semantic force verifier uses the already installed historical `SlotReceipt`. On a miss, the actual TargetReads and full Target receipt are installed before the force receipt is returned. `Ready.store` retains older slot receipts across inventory changes.

## Exact composition after FoldReads are produced

1. `ClassPassPhaseLineage.fold_phase` recovers an indexed source record occurrence, its completed tail, the exact class call, and its later head schedule. It derives captured phase inventories, global bundles, readiness, native histories, and growth from the original supported entry. Equal records still have distinct source indices.
2. `ClassSelectedChildLineage.class_selected` extracts an actual selected call with its earlier and later child schedules. A whole-slot leaf has its exact natural source path and actual captured class forest.
3. `SharedLeafNativeLineage.leaf` consumes the actual semantic LeafReads plus initial native writer History. It derives the historical slot receipt, actual query receipt, returned native request cell or direct branch, and captured writer. Closed target/input operands exclude the unresolved direct branch.
4. `NativeReaderRetention` and the actual suffix reads retain returned cells and recover their writer/ordinary row lineage at the final class-fold reader. The proof must use the actual suffix, not a supplied final-history assertion.

`SourceCurrentNativeEdgeWriterGrowth.History` is the native node/edge request writer history used here. `SourceCurrentNativeMuPublication.History` is a different source-binder publication history. One must not substitute one for the other.

This chain supplies actual query and row-call provenance. It does not supply all-active outer owner exclusion, a decreasing inherited/origin measure, general outer completion, or host forcing correspondence. No new counterexample or Haskell defect is claimed in this audit.

## New literal target history review

`SourceCurrentActualTargetSlotHistory` at SHA `0ba2b6d955b900b0969e1bf98709308a86d13356462d5251ac090e2faf67f158` has no material issue in this review.

Its three History constructors record identity, target-table equality, and a literal completed first write at an absent path. The stored constructor fixes all five target fuels, the class record, captured original forest, and operand-path computation. No future result, support restriction, semantic cache invariant, or read oracle is supplied.

`History.keeps` correctly excludes overwriting an older present target. `History.writer` distinguishes a write to the requested path from a write to another path. It recovers the same complete target value, exact writer entry/return states, and slot-history prefix and suffix. The required initial absence prevents an arbitrary preexisting target from being called a newly produced writer.

The `retained` constructor intentionally constrains only target tables. It permits other state components to differ without a control-transition or heap-growth witness. Therefore History alone is not a complete physical execution trace. Its extracted prefix does not imply Good, Frame, Grows, issued identity retention, or semantic global validity at the writer. The actual worker producers are the source of the history; additional physical or semantic transport must use the actual worker equations and their invariants.

`force` inverts the actual hit/miss worker. `leaf` retains the target table across the exact native return. The generic children/rows combinators accept a recursive-history contract, but `edit_history` discharges that contract by actual edit-fuel induction. Ordinary reconstruction, Mu/union Head, unselected children, and repeated paths all retain the same captured class/forest. `edit_list` handles the literal root-leaf identity branch. `class_call` derives its shared result from the actual runClass equation and starts from exactly the class-local empty slots. It imposes no coherence, active-class, closedness, cap, empty-native-table, or future Read restriction. This broad support is appropriate for its literal-only conclusion.

A force hit after an actual edit prefix can now recover the literal earlier target call from initially empty slots. It still cannot recover the semantic TargetReads or full SlotReceipt without the additional initial-context composition described above. The module header states this boundary correctly.

## New completed native writer consumer review

`SourceCurrentNativeAdmissionWriter.node_written` at SHA `7c42c5daf94d6ede34957123bb4314986ff9ba9804e14b62f269e4adce44defb` has no material issue in this review.

The input facts are initial strong physical Good, initial causal native writer History, SemanticReady, available closed operands, node/edge counter bounds, and domain headroom. The only execution input is the literal successful request equation to verify. The theorem first produces its checked Trace with `NativeKeyAdmission.node_done`. It then transports the initial native History through the actual query. Finally, closed operands exclude the unresolved direct-request case. The result has the exact complete captured request in its returned node cell and the actual earlier `Written` certificate at that handle.

The proof selects the retained winner, including warm hits. It does not equate a losing fresh candidate with the installed result. It derives final History, strong Good, and heap growth. No future Trace, output law, reached range, semantic target receipt, or unrelated final-history premise is present. It does not assert that an arbitrary supplied fuel succeeds.

The native writer History input is explicit and distinct from target-slot History. The conclusion is a physical/causal native request origin. It is not a full language receipt, a general stored Mu body/probe alignment theorem, or a proof of all recursive outer completion.

## Constructed evidence scope

The NativeKeyAdmission `recursive_source` fixture builds a closed source with a used recursive Mu and nonzero physical counters. Its actual checked request is `root/root`. It validates initial admission and the native self branch. It does not execute the nested Mu's unfolding branch. No such stronger fixture coverage is claimed here.

The separate `NativeAdmissionWriterCheck.distinct_recursive_writer` fixture builds two distinct closed ordinary operands. Their children are source-built Mu values. Its actual request returns a nonempty value and allocates more than one native node cell and at least one edge cell. Initial strong Good and causal native History come from the source construction. `node_written` then derives the exact returned request cell, checked Trace, final History/Good/growth, and retained Written certificate. This exercises a distinct cold request rather than the first fixture's self branch. It does not supply a general recursive Mu result-law premise.

The `SlotHistoryKernels.repeated_row_target_history` fixture uses two ordinary rows with distinct symbols, the positive own class `[[0],[1]]`, and repeated productive plain Mu children. It checks its whole class call and exact first-row/second-row schedules. The first selected path starts absent. The next row hits that same target slot. The fixture constructs the prefix slot history and recovers the earlier literal Target call through `force_writer`. Its separate zero-fuel force hits the installed slot; it does not assert a zero-fuel native call. The native self request is retained as raw Steps, without claiming checked Trace Inputs from weak SharedGood.

No new Lean integration is added by this independent review. These three constructed pairs belong to the existing components and are only reviewed here. The existing initial semantic producers and the new exact invariant distinction determine the next action without another example or rank search.

Final reviewed receipts are `slot-history-direct-2`, `native-key-direct-1`, and `native-writer-direct-1`; each strict log has exactly zero bytes. Their respective canonical-1 runs pass with the same known older dependency warning. The full public groups have 15, 2, and 1 declarations. All 18 pairs have the eight explicit options, full signatures and proofs, and only the standard three axioms. The three reviewed constructed groups also pass these checks. This component adds no public declaration, constructed declaration, selected group, or Lean build.

## Minimal bounded alignment proof route

For a recovered writer's literal `TargetWorker.target ... = .done value after saved`, the composition with existing initial numeric support is short:

1. Apply `TargetNumeric.complete` at the writer's actual entry with its captured forest and operand list.
2. Compare the supplied return with that constructed common-fuel return using `target_done_unique`.
3. Substitute all three equalities: complete Value, complete Checked state, and Merge memo.
4. Use the returned TargetReads and TargetComplete.Receipt to install the historical semantic slot receipt. Use the actual prefix's Keeps and Merge Extends to reach the later reader.

The same pattern applies once at a whole class or whole right fold. It supplies all reached lower Reads at once and avoids rebuilding a semantic invariant separately for each observed slot. It still needs the initial Frame/global/domain/reservation facts. A theorem that simply assumes those final Reads would not close this bridge.

Global unfolding/query memo receipts in these interfaces are logical read evidence. The executable workers do not execute the concrete host's global memo lookup schedule. Runtime forcing and correspondence remain separate obligations.
