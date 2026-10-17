# Caller integration and concrete semantic inventory

Reviewed on 2026-10-17 at 05:25 CEST. This review uses the current source at checkpoint f08ebe13 and the additive inventory modules in this directory. It does not change Haskell or older proofs.

## Actual source gate and the older supported endpoint

`cfta/src/Data/CFTA/Equality/Operations.hs:213` partitions classes with `meetsConstrainedMu True`. Lines 236–242 edit each original class path. Each target intersects merged projections at the OTHER paths in the same captured preclass forest. Lines 260–262 reject a reference or interned union, but accept a closed ordinary value with `numNestedMu == 0` before they inspect any guard. Lines 263–270 then handle recursive and longer-path cases. The current Lean gate records that ordinary fast path in `EndpointStatefulGateTrace.lean:24`.

This gate permits more than hereditary leaf inputs. For example, a closed childless ordinary row can have a nonplain own guard and no nested Mu. The ordinary gate still returns false. Such a value has a finite cap of depth 1, but it need not have `Annotated Plain`. This is a proof coverage difference. It is not evidence of a Haskell defect.

The earlier rich editor theorem requires `AtLeaves` or `ListAtLeaves` at `SourceCurrentConstrainedCapRichEditSupport.lean:285`, `:300`, `:316`, and `:332`. Its actual leaf calls `SourceCurrentConstrainedCapSharedSupport.leaf_receipt` at `:193`, which requires `Annotated Plain input` at `:198`. Its captured target is also hereditary. `SourceCurrentConstrainedCapPaths.Supported.root` at `:37` and `root_iff` at `:47` state that the empty mask is exactly hereditary annotation. The ordinary source gate does not imply this requirement.

The new checked joint query can return same-depth caps for mixed operands. It does not prove the older all-path `Preserves` relation for arbitrary newly accepted leaf inputs. If an operand at the other class path has a deeper finite cap, a previously hereditary input can acquire that finite prefix. A general caller theorem needs an explicit output cap-depth bound. It cannot keep the old mask conclusion merely by replacing the leaf query theorem.

## Literal caller order

`SourceCurrentAllocatedTargetGraph.lean:111` defines Fold. A cons evaluates its head Operand, then the shorter tail, then the checked query on that head and the tail result. An Operand at `:36` projects the selected forest and then executes the actual memo-aware Merge. `Target` at `:122` uses Empty for no paths and Fold for a seed and the remaining paths.

`SourceCurrentAllocatedSharedTargetForce.lean:40` retains the complete state on a hit. A miss executes the actual target and then stores that exact returned target. `SourceCurrentAllocatedSharedTargetLeaf.lean:34` forces the target before the checked query. Its query starts at the literal returned checked state. No native table or equality-operation cache resets between these steps.

`SourceCurrentConstrainedCapRichClassSupport.verified` at `:39` captures the current class forest. `SourceCurrentConstrainedCapRichClassPassSupport.fold` at `:77` verifies the tail first. Lines 66–72 pass the actual tail-return forest and its stores to the head class. Any broader depth or origin certificate must follow this same order. A shared-slot certificate must remain indexed by the captured class forest, not the later edited input.

## Existing semantic transport and the extraction

`SourceCurrentAllocatedNativeInputGrowthModels.inventory_agreement` at `:147` derives actual view agreement on the earlier closed roots from record growth and issued-history extension. `SourceCurrentAllocatedNativeAdmittedQuery.inventory_agreement` at `:22` packages exact validity and rank agreement. `SourceCurrentAllocatedNativeContextRebase.contextual` at `:206` transports returned-cell laws. It uses actual request admission and admission of every recorded seen pair. It does not compare unrelated unadmitted names. `SourceCurrentAllocatedNativeAdmissionCache.Covered.rebase` also retains all phases of actual cell admission.

The additive `SourceCurrentAllocatedNativeInventoryRebase.extend` and `rebase` isolate the pre-query part of the existing generated-query proof. They compute the new inventory from the current constructor heap and `old.roots ++ [left,right]`. They preserve the SAME checked state, all native cells, and equality operations. Old root availability follows the actual growth and issued history. New closed resident roots receive computed validity. No query, reached range plan, or desired result law is required.

This semantic transport is independent of the fixed-source cap, occurrence-weight, and original-request store transport. Those must also be established before a result-fed joint query. Rebase alone does not prove cumulative serial headroom.

## Concrete cold model bootstrap

`SourceCurrentConstrainedCapCheckedJointClosed.cold_complete` constructs a full receipt but exports an existential input model and rank family. One cannot identify that model with the concrete finite inventory just from the result. Replaying AdmissionTrace can derive concrete request coverage. It does not derive semantic contextual laws in a different model.

`SourceCurrentAllocatedNativeContextExecution.done_contextual` at `:149` requires `FinishThrough` at `:120`. This contains every actual chosen-model finish law. It is a transport theorem, not a closed supplied-trace semantic producer. The private interpreter in `SourceCurrentAllocatedNativeContextualCompletion` proves the necessary body laws under an arbitrary fixed model, but it has no public arbitrary supplied-trace adapter.

The additive `SourceCurrentAllocatedNativeInventoryCold.pairInventory` computes the concrete two-root inventory BEFORE the query. Its `cold_complete` uses `RecursiveInitialRanges.initial_ranges` at `:51` to derive words from initial source counters and domain room. It then uses `CoveredQuery.query_complete` at `:61` with empty initial contextual and covered tables. It constructs its OWN full checked receipt directly in that computed model and returns `InventoryState.At` at the same actual returned state. It does not reinterpret an arbitrary existential model. A joint trace producer can consume this receipt's own actual trace. This route needs no supplied execution, future contextual law, or additional word-range premise.

## Smallest caller proof still needed

1. Use the actual projection cap theorem at `SourceCurrentConstrainedCapProjection.lean:158` and `:175`. Its depth decreases by the actual signed path length, with the forest slot handled separately. This already covers general finite caps on supplied actual projections.
2. Add a current memo-aware Merge producer with the universal conditional certificate `forall depth, Cap Plain depth original -> Cap Plain depth result`. The earlier `SourceCurrentHereditaryMerge.Certificate` at `:24` proves only `Annotated Plain original -> Annotated Plain result`. It is not the mixed cap certificate. Prove the local candidate law before remember, then read any earlier keep-first winner from its exact captured-original certificate. Preserve causal Mu, semantic, and native stores through actual comparison effects.
3. Compose actual Operand and Target/Fold cap production with the checked joint query. At each native query, use the maximum of the two actual operand cap depths. Derive the selected target's depth from the immutable captured forest and actual operand paths. Retain the new semantic inventory, original-request origins, and joint stores at the actual return.
4. Lift this through Force, Leaf, Edit, and the tail-first ClassPass. State the cap-depth transformer that the compiled selected positions require. Do not claim arbitrary ordinary gate acceptance gives hereditary placement or preserves every older mask.
5. Prove general selected outer progress and cumulative resource admission. The finite ordinary initial-resource root and the mixed plain-node endpoint cover their stated domains. They do not establish whole-library constrained recursive reduction termination or concrete GHC/Haskell execution transfer.

The present extraction closes a pre-query semantic transport boundary and the concrete cold-model bootstrap. It does not close the general caller pipeline or the full root proof.
