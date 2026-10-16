# Checked shared target slots and leaves

Read-only design audit, 2026-10-16 08:50 CEST. No proof source edit or build ran. The new TargetGraph and TargetComplete APIs are still being implemented. Names below are proposed interfaces, not claims that these declarations already exist.

## State and stored history

Use `State width` with three fields: `checked : SourceEqualityNativeDemand.State width`, `targets : Path → Option Value`, and `memo : MergeMemo`. `initial checked memo` clears only targets. `advance state checked` retains slots and merge Memo. `store state path value checked saved` updates one slot and takes the exact returned checked state and merge Memo.

Keep the captured class forest and base heap as Ready parameters. They remain fixed through every edit within that class. A minimal `Ready formulas solver inventory record values base state` contains current ClassScan.Ready, current InventoryState.At, Keeps from base to the current heap, current merge Stored, uniform ambient CacheCovers, and a historical SlotReceipt for every present slot. Global tables and the fourth memo can remain explicit graph/receipt indices instead of new State fields.

`SlotReceipt formulas solver record values heap memo path value` contains path membership and existential historical start/return checked states, merge memos, global tables, and input/output inventories. It retains the actual new Target graph and the derived TargetComplete receipt for `operandPaths record.paths path`, plus Keeps from that historical return heap to heap and merge Extends from the historical saved memo to memo. Use the exact captured `values`. Do not replace these values with the currently edited forest.

The historical inventories must be existential and need not equal the current Ready inventory. Native queries can expand that inventory after a slot is stored. The completed target language is stated in fixed independent PCS meaning and remains valid across that change. A hit needs availableclosed output and historical CommonIncludes, not new admission of that output into an old input model. The next actual generated native query derives admission when requested.

## Minimal bookkeeping lemmas

- `SlotReceipt.grows receipt keeps mergeExtends`: compose heap Keeps and merge Extends. It retains the same historical graph and inventories.
- `SlotReceipt.available receipt`: use its historical target receipt's availableclosed output and current Keeps.
- `SlotReceipt.included receipt coherent active ...`: turn historical CommonIncludes into acceptance of the selected class subterm. Reuse `operandPaths_nonempty`, `operandPaths_nonroot`, `EqualityNormalize.class_pair_equal`, and `SourceEqualitySelectedRequired.lookup_natural`.
- `initial_ready`: take the current full Ready, At, captured Keeps, Stored, and uniform CacheCovers. Empty slots have no historical obligation.
- `Ready.advance`: accept a derived next checked Ready, next inventory At, and Keeps. Keep the merge Memo and slots unchanged. Grow Stored and every SlotReceipt. This bookkeeping lemma may change the inventory parameter; public completion must derive its next At from the actual query receipt.
- `Ready.store`: consume the same actual finite target receipt. Use its returned Ready/At, Keeps, Stored/CacheCovers and merge Extends. Store that historical receipt at the new slot; grow every other slot's history.

`SourceCurrentMemoSharedTargetState.lean:26-42,45-65,86-104,140-190` is the structural blueprint. Its old native execution or IdleReady proof is not reused.

## Force and finite first demand

Define raw `Force record values path before value after` with only two source branches: hit reads `before.targets path = some value` and returns the identical full State; miss reads none, executes the new actual TargetGraph at `before.checked` and `before.memo`, then stores its exact return. A raw miss constructor must not take desired future Ready, At, language, or a TargetComplete receipt as an assumed callback.

`ForceRanges` is True at a present slot. At an absent slot it is exactly the new TargetRanges for the ordered other paths and the actual initial checked state/merge Memo. Initial Values at the base, selected ForestClosed domains, and captured Keeps derive all target operands' domains. Reuse `SourceCurrentTargetPathComplete.operand_domains` (`:267`) unchanged.

`Force.complete` should return the actual Force graph, a derived next inventory, full Ready, Keeps, availableclosed target, the stored path equality, Retains for older slots, merge Extends/Stored/CacheCovers, and actual global receipts. A hit has no new native request, merge call, field allocation, or global read. A miss uses TargetComplete once at the actual state. To verify an independently supplied actual Force trace, use TargetComplete.verified or target graph uniqueness to identify the derived finite receipt with that same miss. Do not assume successful future target completion.

## Leaf and semantic contract

Define raw Leaf as Force first, then the new checked QueryStep with operands `target,input` at the returned checked state. Advance the shared state with that exact checked query return. The query retains the merge Memo and slots. Its Keeps grows Stored and all historical slot receipts. Its actual receipt supplies the next inventory At, same-cache Fields, availableclosed result, exact intersection meaning, and global receipt. Native tables/domains and operations can grow; they must not be reset or claimed unchanged.

`LeafRanges` contains ForceRanges and only the reached WordRanges for `requestNode emptyDomain target input` at each actual Force return. Initial availableclosed input is sufficient. The later structural edit proof derives this input closure from the selected path domain and edit safety, without whole-forest closure. The finite endpoint must derive intermediate Ready/At/Fields and both actual operations from these initial facts and reached ranges.

The new query helper is now saved as `SourceCurrentAllocatedTargetQuery.Step left right before value after`. Its raw `.run` records the actual checked PhysicalTrace. `finite formulas solver inventory left right before ready admitted leftAvailable rightAvailable leftClosed rightClosed ranges memos valid` returns a computed next inventory, value, state, source/roots equations, and `Receipt formulas solver next left right before value after memos`. The receipt contains actual, ready, admitted, effects, extension, available, closed, exact meaning, global validity, and actual NoGlobal events. `Step.verified` gives that receipt for an existing actual Step; `Step.unique` proves value and complete checked-state equality. Use this helper with left=target and right=input. The helper source was inspected before its first canonical build; this note does not report its build result.

Exact intersection gives unconditional narrowing to the concrete leaf input. Historical target CommonIncludes plus class satisfaction gives conditional retention of an accepted selected input subterm. Use the old `Leaf.keeps_term` proof shape, but obtain semantics from the new checked query receipt. No universal raw conjunction law or old Scoped.Step is needed.

## Tables and remaining scope

Targets are class-local. The completed merge Memo is warm across classes. Native caches/domains, equality operations, global unfolding/query tables, and the fourth emptiness memo remain warm too. Force/Leaf do not call the fourth memo: retain its contents and transport Correct through their Keeps. Combine target reads before the same actual native query receipt; retain prior global unfolding entries and both query tables.

The actual noConstraint selection callback, Top CAF demand/identity, HashMap iteration, lazy forcing, and pending publication remain runtime adapter boundaries. This design does not identify those runtime effects with a completed serial graph. It also does not complete structural class edits or the outer constrained caller.
