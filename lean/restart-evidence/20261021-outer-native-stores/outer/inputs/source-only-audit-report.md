# Completed outer native-store audit

This is a source-only audit. It adds zero Lean, Lake, canonical, or public proof commands. The proposed statements are not elaborated or proved. The verifier checks snapshots and scope metadata. It does not check a new mathematical proof.

## Result

Normality and initial prefix resources already have independent producers. The missing proof is narrower: carry the four new store laws through the actual completed outer phases, then through the existing literal prefix steps. Keep the old semantic and resource producers. Do not reconstruct their full receipts.

The four laws at one caller `before` are:

1. `NativeRequestPositivePositions.Support before.checked.native.machine.heap before.checked.native`.
2. An actual `NativeMuPublication.History empty before.checked.native.machine.heap`.
3. `ConstrainedCapMemoMerge.Stored Plain before.merge`.
4. `MergePositivePosition.Support before.merge`.

Here `Plain guard` means `SourceMemoGate.plain guard = true`. The third law is conditional for every finite cap of the same captured Merge input. It does not assert that every cached input or every forest root has a finite cap. The fourth law uses the full captured Merge original and the same positive path. Native Support and Merge Support are distinct laws.

## Exact entry package

Use the SAME caller, inventory, source memo bundle, and seed as `OuterInitialActual`:

- `Context formulas solver inventory before memos`.
- `Frame formulas solver inventory before.checked`.
- `Fits seed.2 before.checked`.
- `SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) before.checked.native.machine.heap`.
- Phase inputs: ready inherited constraints and available node, resident edge, resident edge list, or available node list, as specified by that exact phase.
- `Room bits (OuterInitialSchedule.phase fuel budget seed).2`, with width `bits + 2`.
- Initial `UnionNormal` and the four laws above.
- The literal completed worker equation for that same phase, request, fuels, and full caller return.

The carrier concerns all resident raw edge guards in the exact heap. It is not a Plain predicate and not merely a fact about the selected row. Room is the existing scheduled capacity premise. It is not derived from a successful return or from arbitrary machine width. `Frame.current` already supplies `CurrentNative.At Plain`; do not add a redundant Current input.

Sources: `OuterInitialActual` 49–129, 432–543; `ConstrainedCapGeneratedQueryResources` 61–73; `ConstrainedCapOperandFrame.current` 31–36.

## Normality is already available

`UnionNormalLocalParent.parent` 118–135 preserves normality at the state of every literal Parent outcome. It covers raw rejection, failed lookup, local failure, unchanged returns, empty returns, and completed class work. It requires no finite input cap or successful-return assumption. Rewriting by the SAME observed `.done` equation gives normality at its exact returned state.

`UnionNormalOuter` 218–264 exports all eight relevant completed/stopping phase facts: node_call, node_body, edge_call, edge_body, row_pass, descendant_pass, child_pass, and indexed_walk. The statement is about every stopping outcome, so using it at a completed sibling is valid. No new all-branch normality proof is needed in GeneralParent or the new outer induction.

`OuterUnionNormalHistory.reached` 63–70 also carries normality through an actual unfinished prefix. `stopping` 89–94 preserves it at the subsequent stopping outcome. These facts do not supply the four new store laws.

## Minimal proof decomposition

A store-only strong induction on the existing outer fuel is sufficient. It has the same six internal cases as `OuterInitialActual.all_actual` 416–429. It must NOT copy that file's old Context, physical effects, language, read, and resource inductions.

At each completed head, call the existing public old endpoint to obtain its exact `Post`, returned Frame, Fits, Carrier, availability, and chosen global memo bundle. Apply the new store induction to the SAME literal head return. Its four conclusions depend only on that returned caller, so they combine with the old chosen context without a claim that independently selected memo bundles are equal. The next induction call uses the exact old returned context and bundle. This is proof reuse on one actual completed return; it is not another execution.

The smallest useful public interface is:

- `edge_call`: a store transport theorem on one supplied, fixed `EdgeCallNumeric.Receipt` plus its genuine initial resource premises.
- `node_call`: completed node-call store preservation.
- `descendants`: completed descendant store preservation.

The last two require all six internal induction cases. The three public heads suffice for a later actual-prefix proof: rows_edge needs edge_call; rows_tail needs edge_call then descendants; walk_tail needs node_call. Body/rows/children/walk facts can remain private until a consumer needs their public statements. Exporting their direct wrappers is inexpensive, but is not necessary for the next prefix producer. `proposed-signature.lean.txt` gives the explicit three-head shape without a new public invariant type.

### Edge call and SAME numeric receipt

Keep the old `EdgeCallNumeric.Receipt` as a parameter. It already fixes the actual graph, strict reads, result, complete caller, inventory, final global bundle, and literal replay (`EdgeCallNumeric` 59–83). The additional store proof does not replace that receipt or select another writer for it.

- Ready hit: `EdgeCallNumeric.ready` 85–104 derives literal `after = before`. All four laws follow at that same caller. No past writer-entry law is inferred from a ready reader.
- Evaluate: use the SAME `beginEdge` event. `edge_start` recovers the actual captured request and its resident input/inherited readiness. `beginEdge_components` retains checked state, Merge, and fourth literally. Transfer the four inputs and normality to that same running caller.
- Use `ParentAlphabetReservation.resident_reserved` 53–111 when the caller has the carrier plus the existing uniform reservation. If the helper takes `EdgeCallNumeric.Reserved` directly, reduce it at the SAME evaluate event. This is a genuine initial reservation, not a future Parent-entry callback.
- Recover the literal parent return from the retained EdgeCall receipt's `.run` and the evaluated worker equation, or invert its SAME `.actual` body and use `AllocatedParentWorkerCompletion.edgeBody_complete` 56–64. Both routes fix the full checked state, fourth, Merge, result, and captured owner.
- Derive `ParentNumeric.LiveInputs` at that running caller from its resident edge, actual field read, inherited readiness, and cached original children. The exact model is `ParentNumeric.resident_complete` 228–248. Raw rejection uses a dummy loaded value only on the branch where the live condition is false.
- Apply the forthcoming `ActualParentNativeStores.parent` to this SAME literal Parent return. That producer may internally return a numeric receipt and memo bundle. Use its four state-indexed conclusions, and keep the supplied old EdgeCall receipt unchanged. Do not claim the two global bundles or receipt existentials are identical.
- `finishEdge` changes only the outer result cell. The checked state, Merge, and fourth remain exact. Transport the four conclusions by those literal equalities.

The GeneralParent producer is a pending dependency in this audit. Its frozen source-only plan and proposed signature are copied as inputs. This audit does not count that plan as a checked theorem.

### Six internal completed cases

| Phase | Actual order and extra-law proof | Existing resource source |
|---|---|---|
| node_call | Ready hit is unchanged. Evaluate transfers to the SAME captured owner, recurses on its body, then finishes only the outer node cell. | `OuterInitialActual` 131–169; actual node start/finish and literal checked retention. |
| node_body | Empty and union retain caller. Resident Mu cleanup also retains the ENTIRE caller. Ordinary node runs rows, then literal modifyNode. | `OuterInitialActual` 346–414. |
| rows | Actual edge call, actual descendants, actual row suffix. Apply new edge helper, descendant IH, then row-tail IH. | `OuterInitialActual` 291–344. |
| descendants | Actual inherited-first prefix, actual children, actual raw edge reconstruction. | `OuterInitialActual` 244–289. |
| children | Contradiction erases children with unchanged caller. Live payload delegates to indexed walk. | `OuterInitialActual` 220–242. |
| walk | Actual equality descent at index, actual node call, actual tail at index+1. | `OuterInitialActual` 171–218. |

Do not infer positive ancestry of a Mu cleanup result in the Mu case. `MuReconstructionEffects.node_body` 60–74 and `AllocatedMuRebuild.resident_rebuild` 142–159 already show literal no-op caller effects under the existing probes, coherence/readiness, and residency. This is sufficient for store preservation. It is stronger and smaller than a new opaque-Mu positional law for this branch.

For equality prefix/descent, the physical heap and native tables and Merge stay literal. The four laws transfer directly even though equality operations change.

For raw edge and ordinary node rebuilds, reuse `AllocatedPartialStepEffects.raw_edge` / `.modify` for the actual returned context. Their `AllocatedRawRebuild` receipts explicitly provide Extension and literal native node/edge table equalities (52–63), plus exact actual constructor returns. Use `NativePositiveSupportAdvance.advance` on the SAME constructor interval and derive its before Current from the old Frame. Use exact makeEdge nodeRecords equality for `History.retain`; for changed makeNode use `InternedShallowHeap.makeNode_noNewMu`. The unchanged modify branch is literal identity. Both Merge tables remain exact. Growth alone supplies neither new native Support nor a causal publication History.

## Exact resource schedule

Retain `OuterInitialSchedule` 39–74:

- `node f = body f`.
- `body (f+1) seed = rebuild (rows f seed)`.
- `rows (f+1) seed = rows f (descendants f (parent seed))`.
- `descendants f seed = rebuild (children f seed)`.
- `children f = walk f`.
- `walk (f+1) seed = walk f (node f seed)`.

Thus a row head starts with `edgeSeed = parent budget seed`; its descendants start with that returned edge seed; the row suffix starts with `descendants fuel budget edgeSeed`. A walk tail starts with the exact node head schedule at the same smaller fuel. Use the existing `*_ge` and `parent_reserved` (123–151) to extract sub-call Room. Do not feed the initial seed to every sibling or assume a later query range.

## Existing unfinished-prefix producer: corrected boundary

`OuterInitialPrefix.reached` 263–286 ALREADY returns, for the SAME actual `Reached` proof:

- the exact current `SeedTrace`;
- a Post and current Context through that Post;
- current Frame, Fits, Carrier, and phase Inputs;
- current forecast Room and bounds relative to the initial forecast;
- the phase fuel-need bound.

It uses initial Context/Frame/Fits/Carrier/Inputs and initial forecast Room. It requires no future completed outer outcome. Its rows_edge, rows_tail, and walk_tail branches use only actual preceding completed siblings (170–237). This corrects the earlier broad claim that all unfinished-prefix resource production was unavailable.

Once the completed store endpoints exist, a small additional `Reached` induction can carry the four new laws. The nontrivial steps are precisely rows_edge, rows_tail, and walk_tail above. Activation and equality-only prefix/head steps use literal checked/heap/Merge retention. Take exact current old resources from the existing prefix theorem, with the current seed and SAME prefix proof. Normality is independently available from `OuterUnionNormalHistory.reached`.

This still does not establish unconditional entry Room/Frame/Context for arbitrary programs or arbitrary raw successes. It does not turn a worker `.done` equation into physical native admission without the genuine ranges/resources. No completed enclosing class or future outer return is an allowed premise at an unfinished cut.

## Historical writer boundary

A later ledger must place the resource Context/Frame/Fits/resident reservation and all four new laws in ONE existential writer entry, with one caller, memo bundle, inventory, profile, exact captured request, and actual Parent done equation. Existing `OuterSupportedParentHistory.SupportedWritten` 44–56 stores an old writer tuple, but not this full package. An old writer existential conjoined with a separate new entry existential does not correlate the witnesses.

Completed transport plus the short actual-prefix store extension can supply cold entry laws in the explicit initial-resource scope. A new ledger can then install that joint entry at the actual finish. This audit does not propose copying its old 551-line proof or claim a warm reader reconstructs earlier entry laws by reverse growth. Arbitrary-start resources, global owner exclusion, outer termination, native refinement, and a global renewal rank remain open.

## Authorship and verification

I authored `NativePositiveSupportAdvance`, the original `NativeRequestPositivePositions` proof, `NativeCurrentPositivePositions`, and `ActualParentScanNativeStores`. They are dependencies or prior work, not independent proof-review subjects here. I also authored some earlier projection/cap components. I did not author OuterInitialActual, EdgeCallNumeric, the old normality/resource prefix modules, or the forthcoming GeneralParent producer. This report audits their exact contracts and composition route. It does not claim independent review of my authored proof bodies.

All source pins contain whole-file SHA-256 hashes and exact reviewed line ranges. Portable verification checks the copied files. `--live --root ROOT` also checks those whole-file hashes in the current checkout. The verifier makes zero Lean/Lake/canonical calls. No official source, frozen prior package, docs, or Git metadata changed.
