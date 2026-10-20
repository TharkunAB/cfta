# Next producer after rooted source-child focus

Reviewed 2026-10-20 16:54 CEST. This is a bounded read-only design audit. It runs no Lean or runtime job. It changes no candidate, repository, or frozen package. The inspected RootedRowChildOrigins draft has SHA256 `2186d2dc0c3079a2c669a48649230c314b7b6c56685836377c146b9969471214`. Its check and promotion remain the author's work. During this review the draft changed only typed Nat indices and the local spelling prefix to earlier. The revised draft was reread. An exact reviewed snapshot is retained so this report does not freeze the author's mutable draft path.

The next useful actual producer is a **selected stored-body child resume with an exact initial-cell alternative**. It should recover the earlier selected writer from one actual completed source call, then resume that SAME writer's original body source. It should not assume a Written receipt or equate the current callback with that writer. No new general ancestry relation is needed for this step.

## What the draft now supplies

Origin.node retains the actual source RowCall, complete selected parent row, exact indexed child source call, ordered prefix and suffix, joint Context, physical and issued growth, rooted Reached, and a strict original syntax bound. Its union induction follows actual original source member calls and their entry heaps. It does not infer same-leaf membership through source union normalization.

Origin.capture retains the exact input slot, the complete captured value, RowAt of the selected parent row in that value, its selected child, and Reached at the variable call. Origin.binder retains both current probes, the actual request, the exact selected complete Mu record, finish, RowAt in that selected stored body, the selected child, and Reached at the CURRENT binder. These last two branches are explicit stops. They do not claim the captured value's earlier compiler binding or the selected payload's current-callback ancestry.

## Capture can already be classified inline

Reached is an existential actual Path plus forward growth for each recorded callback crossing (`InternedFreshOrdinarySourceHistory`, lines 18–22). For the capture branch, expose that Path and apply SourceCaptureOriginalSlots.original_slot, lines 39–47, to the exact input lookup and RowAt parent row. This gives an exact originalSlot and `slot = crossings.length + originalSlot`, with the SAME captured value in initial[originalSlot]. No new producer or all-input freshness assumption is needed for this short composition. If initial is literally empty, empty_initial excludes the branch.

That last corollary does not apply to native reconstruction. Actual repaired execute at `InternedFreshOrdinaryStoredSubstitution`, lines 76–84, builds the full encoded body with initial inputs

```text
(leaves body).map (input (selfEnvironment entry body depth ordinary)).
```

Those inputs are not empty. In this exact native case, compose the resulting indexed original-input lookup with NativeSelfCaptureSlots.lookup, lines 20–44. The result is the SAME indexed closed leaf, unchanged, or the SAME indexed own-reference leaf mapped to the COMPLETE selected Mu. Other literal references cannot carry RowAt. No Coherent/Values premise is needed for this direct indexed lookup. The separate canonical_slot endpoint requires its explicit Coherent, Values, and leaf-membership premises; it must not be used to identify an arbitrary repeated occurrence with findIdx.

The native capture split is an input classification, not a compiler-source origin or decrease. A closed leaf can equal the entire closed body. The full-self arm can return exactly the same complete Mu. Neither case justifies a strict stored-value or original-binding measure. A new public wrapper that only repeats these two existing lemmas would add little; keep this classification in the eventual native consumer unless an actual reuse appears.

## Exact next actual producer

A minimal endpoint, provisionally `selected_body_child_or_prior`, can take:

```text
root, initial, before, Context before initial,
result, reader, build root initial before = done result reader,
key, entry, body, depth, ordinary,
reader.nodeRecords key = some (mu entry body depth ordinary),
parentRow, RowAt body parentRow,
childIndex, child, parentRow.children[childIndex]? = some child.
```

It should return either the EXACT full record already in before.nodeRecords key, or ONE fixed publication event with all of these linked receipts:

- Its key, entry, body, depth, and ordinary fields equal the selected full record. Its first-write-none fact, original rooted binder Reached, issued prefix/probe/body paths, and writer-to-reader physical and issued suffix remain in the SAME event witness.
- Its actual reserved raw source build, exact raw-to-stored self filter, joint Context, rooted source-body Reached, and SourceRow for the SAME parentRow remain at their historical heaps.
- `RootedRowChildOrigins.Origin root initial event.expression parentRow childIndex child` resumes that actual writer source, with the SAME selected row and child.

The proof is a concrete composition: CompletedBuildRootedWriters.build_writer_or_prior (lines 334–346), PublicationBodySourceRows.written_body_origin (lines 71–103), then the draft's from_source_row. The latter receives the actual allocated Context and source-body Reached returned by written_body_origin. All equalities must stay under the same event existential. Do not select an unrelated second publication or independent raw callback.

An existing binder-stop cell at its local after heap can be moved to this actual root return reader using an explicit forward Grows suffix and its nodeRecords field. This is only physical selected-record retention. It does not create a rooted writer from arbitrary History or growth. The endpoint itself can consume the selected reader cell directly, so it need not add unused local-schedule parameters.

For an empty or otherwise Mu-free initial heap, build_writer removes the initial-cell alternative. This is a real special case, not a replacement for the general warm-start contract. The producer uses an already completed Fresh source call. It asks for no future outer-worker return and no semantic ancestry law.

The draft's capture and binder constructors keep Reached but do not expose a terminal binder-syntax bound against Origin.original. The node constructor does expose childSyntax strictly smaller than Origin.original. The proposed selected-writer resume needs no additional current-binder bound: it resumes the earlier writer's actual source and derives the next node bound against that writer expression. Do not strengthen Origin only to supply an unused bound. A Reached path can relate its reached syntax to its root; it does not by itself relate an arbitrary reached syntax to the phantom Origin.original parameter of a manually constructed capture or binder witness.

## Why this does not yet give a global original-binding measure

A warm native encoded build normally starts in a heap with completed Mu records. build_writer_or_prior correctly permits the selected exact record to predate that build. The current callback's Reached receipt does not root that old publication. NativeMuIssuedWriters can recover a physical earlier publication from an actual issued path, but its general Written receipt has no original source-root Reached. Those two facts must not be silently combined into a rooted earlier writer.

The needed next history consumer must carry the initial record's actual rooted source provenance from the earlier source-built phase, or retain the initial-cell stop until that provenance is supplied by a real preceding execution. It must also keep different roots explicit: the generated native encode root with mapped leaf inputs and the earlier original compiler source root are not interchangeable.

Even in the newly produced writer arm, the historical writer expression can be larger than the CURRENT callback syntax or belong to a different source branch. The strict bound obtained after resumption is against event.expression, not the current callback. The full-self capture arm can re-enter the same selected Mu. Therefore a global decrease cannot follow from local syntax size, initial input count, or selected value depth alone. The existing first-write and actual issued paths retain useful causal structure; no well-founded mixed source/writer measure is proved by this review.

The immediate action is to implement the selected-body child fork after the rooted focus is checked. Inline the exact capture classification in its native consumer. Preserve the explicit initial full-cell alternative, complete selfMu arm, closed-root stopping, and occurrence-versus-slot distinction. This advances a selected historical source handoff without asserting global binding ancestry, termination, observation invariance, or a Haskell defect.
