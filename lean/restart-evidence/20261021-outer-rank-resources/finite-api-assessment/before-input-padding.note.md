# Finite fold API for successful C resources

This is a source-only assessment at 2026-10-21 16:40 CEST. It changes no proof, official source, or frozen package. It runs no compiler, runtime, or proof job. The proposed physical endpoint remains conditional on one observed successful node call.

The checked `stage_bounds` and `retains` do not provide the whole local interface. They provide the total Room bounds. The direct exact-output proof also needs a private one-rank equation and Seed-only chronological fold facts. It does not need a second rank induction or numeric work/lower-fuel proofs.

1. Use public `stage_bounds` at the actual row index to bound the Parent image by the current node's C output. Apply `Room.mono`, then `parent_reserved`. Use its selected-child output bound to supply the child induction hypothesis's Room. Keep the original global initial packet and literal Reached cuts for semantic receipts and rank. These Room uses do not require a new global Schedule comparison. [S1:205–238, S3:105–115, S4:146–151]
2. Total coverage does not state `childOutput.seed ≤ nextSlot.seed`. Derive this at the SAME current seed by finite candidate membership, `cover_member`, and membership in the appended guard list. Derive `current.seed ≤ nextSlot.seed` from `cover_ge` and append-left membership. No comparison of C at different input seeds follows. [S1:206–216, S5:51–68]
3. Keep `B = parent(rowPrior.seed).mass` fixed throughout that row. If k actual children have completed, the actual checked state fits the literal k-slot prefix. Prefix/suffix retention pads k to B. Apply the existing raw edge endpoint at the k-prefix seed, then `profile_mono` to bound that raw rebuild by the numeric rebuild after B slots. This is exactly the next row seed. [S1:217–222, S6:42–45, S7:49–68]
4. After the actual rows finish, pad the actual row count to the owner's mass. Apply the existing raw node endpoint and the same constructor monotonicity. Identify the final numeric rebuild with C.output using a one-rank equation. Public `retains` only gives entry-to-output bounds; the public stage conclusion does not state this final rebuild identity. A different domination argument is not ruled out, but no checked public endpoint was found that removes this equation from the direct route. [S2:55–75,149–155; S7:70–95]
5. The public-only unfolding route is already checked in the stage module. It unfolds public `envelope`, uses core `WellFounded.fix_eq`, proves recursive-function/pair eta by funext and pair cases, and uses explicit `List.attach_map_val`. Its equation and all finite helper names are PRIVATE. The new module must prove its own short equation through public envelope, not call those names or define another recursive C. Literal abbreviations for the existing header's images/row/slot expressions suffice. [S1:13–52]

The minimum proof obligations are these. The counts are estimates for ordinary rendered source, with separate lines for proof steps.

| Private obligation group | Estimated lines |
| --- | ---: |
| Literal finite abbreviations and public-root one-rank equality | 43–55 |
| Seed-only fold retention, range cut, and prefix padding | 22–30 |
| Slot entry/candidate inclusion and candidate membership | 20–28 |
| Row entry retention and local rebuild identification | 15–25 |
| Total | 100–138 |

This is approximately 7–9 private proof facts plus finite abbreviations. The grouping is not a new public interface or a required declaration count. Use direct conjunctions of profile Le and alphabet inclusion. A private generic fold lemma may take its locally proved one-step growth fact; the public physical theorem takes no callback or supplied resource law. Existing `Fits.mono` handles state widening. Carrier widening is the direct application of guard-list inclusion to `Heap`. [S8:33–59, S9:14–16]

The fixed-B mass fact is smaller than a slot-state invariant. The SAME successful Parent endpoint returns Fits at its Parent profile and returned-row residency. `resident_children` then bounds every original returned child mass and the list width by B. Earlier slots retain that literal child list. Seed-only slot retention gives B at most the current seed mass. This establishes candidate mass membership without a separate physical stored-mass proof at every slot. Fits and carrier at each actual slot remain needed for executing the conditional resource induction. [S10:104–119, S11:97–108]

No new W, L, maximum, or worker-offset proof is needed for this conditional result. The checked stage theorem already supplies the total profile bounds for Room. The new local helper facts compare only one computed trajectory, not different initial seeds.

A smaller useful numerical checkpoint, if a separate scope is desired, is the exact one-rank equality together with candidate-to-next-slot and prefix-padding Seed bounds. This would remove the actual missing finite API. It would not establish any physical correspondence. Keep these facts private in the successful-resource module unless reuse justifies a separate concrete public theorem. A successful-walk lemma with a supplied child resource callback would not resolve the missing proof and is not recommended.

Budget assessment: 350 total lines is optimistic. About 100–140 finite lines plus about 60 header/import/context lines leaves 300–340 physical lines under a 500-line stop. One node-fuel induction with local row and child-list inductions is plausible within that remainder, but not established without the rendered source. The main risks are SAME-cut semantic resource extraction, complete captured-request equality, and the Mu/node-demand cases, not finite arithmetic. There is no reason here to duplicate a six-phase semantic framework.

The assessment does not prove a successful-call resource endpoint, adequate fuel, initial capacity, all-prefix C correspondence, or actual nested lower-fuel coverage. It does not infer a historical writer from a current reader. I authored C, the stage proof, OlderOwnerLineage, ActualParentNativeStores, and OuterPrefixNativeStores. This assessment is not an independent review of those foundations.

## Source index

- S1 `lean/MicroCFTA/SourceCurrentOuterRankEnvelopeStages.lean`: 13–52, 62–103, 120–132, 205–240. Checked 242/6183fb57. The private source is evidence of a checked route, not an importable API.
- S2 `lean/MicroCFTA/SourceCurrentOuterRankEnvelope.lean`: 55–75, 149–155. Checked 157/b8401732.
- S3 `lean/MicroCFTA/SourceCurrentAllocatedNativeResourceForecast.lean`: 105–115.
- S4 `lean/MicroCFTA/SourceCurrentOuterInitialSchedule.lean`: 17–37, 146–151.
- S5 `lean/MicroCFTA/SourceCurrentInitialSelectionForecast.lean`: 51–68.
- S6 `lean/MicroCFTA/SourceCurrentOuterConstructorBounds.lean`: 35–45, 71–89.
- S7 `lean/MicroCFTA/SourceCurrentOuterRebuildGuardAlphabet.lean`: 49–95.
- S8 `lean/MicroCFTA/SourceCurrentConstrainedCapGeneratedQueryResources.lean`: 33–59.
- S9 `lean/MicroCFTA/SourceEqualityAnnotationHeap.lean`: 14–16.
- S10 `lean/MicroCFTA/SourceCurrentOuterEdgeGuardAlphabet.lean`: 104–119.
- S11 `lean/MicroCFTA/SourceCurrentAllocatedNativePhysicalMass.lean`: 97–108.
