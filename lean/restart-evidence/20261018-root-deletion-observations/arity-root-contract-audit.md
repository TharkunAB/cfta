# Root deletion contract audit

Reviewed on 2026-10-18 at 19:50 CEST. This is a source review. No Lean job or production edit was made for this review.

The proposed observer has the correct order for the actual root filter. It deletes an original bare reference before profile assignment. It follows original root union members. It leaves an original node or Mu atomic. In particular, it must not delete a reference that substitution or a later Mu reconstruction exposes. I found no actual-publication counterexample to the proposed tagged deletion invariant. This review does not prove that invariant.

## Necessary input relation

`ScopedProfileInputs.Compatible` alone is insufficient for a general source deletion comparison. It equates assigned profiles on live fixed names and paired varying names. It does not equate deletion tests. For the source `.var 0`, let its two varying names be distinct `x` and `y`. Assign the same nonempty profile to `x` on the first side and `y` on the second side. If the first cut deletes `x` and the second cut retains `y`, the deletion observations differ. This follows directly from the reference clause of `deleted`; it is not a new checked counterexample or an actual-publication failure.

A general comparison must also require:

- Equal cut decisions on each live fixed name.
- Equal cut decisions on each pair of live varying names.

The binder extension must shadow both the assigned profile and the cut decision with the same local values. The existing live alias condition is needed to make these two overrides agree on captures. Do not require freshness of unused captures or dead rows. The relevant existing definitions are `ScopedProfileInputs.Compatible` at lines 27–30, `extend` at lines 86–117, and `extend_depth` at lines 120–129. `StoredRootDeletion.congr`, lines 70–94, already keeps the two support conditions separate for a single stored value.

For one actual publication, the intended tagged test is suitable: classify the reserved name `q` and the ordinary name `r` as the local label on their respective sides; classify every other name by its external reference. Test those labels directly. Do not first map external labels to physical names and then merge an external label with the local label. `UsedBinderAliasTransport.publication`, lines 136–147, supplies the actual local alias extension. `ScopedProfileInputs.publication`, lines 161–185, supplies profile compatibility from the actual ordinary and reserved freshness facts. A corresponding cut-compatibility extension remains to be proved.

## Actual binder proof route

The two normalized callbacks are actual historical builds followed by actual filters. `NativeMuPublicationCallbacks.raw_callbacks`, lines 47–97, exposes both builds, both filter results, their entry contexts, and their growth into the pre-publication body heap. These are the correct source points for strict-body induction. They do not identify either raw result with the stored result of an unrelated writer.

`NativeNormalizedComparison.probes_same`, lines 295–314, already proves equal `usesLocal` decisions for two complete probe pairs from the same symbolic source and fixed input presentation. Its hypotheses include the actual contexts, depth heaps, and four completed callbacks. It has no extra alias premise. Thus the source comparison can split the same retained/unused branch on both sides.

For a retained Mu, `deleted` is the unfiltered `denote` of that Mu. The proof must use the empty-cut instance of the stronger payload invariant and the existing retained-Mu profile reduction. It must not pass the outer cut predicate into the retained body's root alternatives. Such a step would delete references that the actual root filter cannot see.

For smart-unused cleanup, actual history gives a stronger shortcut than a profile comparison. `NativeNormalizedComparisonExecution.history_unused`, lines 417–423, proves:

```text
History empty reader
  + reader contains the exact selected Mu record
  + usesLocal depth ordinary = false
  => finish true selectedMu = eraseSelf ordinaryName ordinary
```

This is an exact value equation. It covers nested binders. A causal proof from empty tables can therefore reduce the unused result to the current ordinary probe. It need not assume that an earlier writer body has the same original root structure as that probe. The history must reach the exact reader that contains the selected record. A bare `Grows` relation or an arbitrary coherent table does not supply this premise.

If the intended theorem starts from an arbitrary stronger heap without an empty-table history, it needs a corresponding initial unused-readback law or a separate derivation. `StoredMuUnusedProfile.smart_unused`, lines 22–58, proves only unfiltered profile equivalence from the old payload contract and depth correctness. That theorem alone does not prove deletion equivalence.

## Standalone references and normalization

The actual filter keeps a standalone reference. `StoredRootDeletionFilter.singleton`, lines 53–69, restores this exception, and `filter_profile`, lines 72–79, connects it to the actual ready filter. Thus equality of deletion observations alone is insufficient: retain equality of the tagged bare-root result as planned. `UsedBinderOutputTags.scoped_bare`, lines 138–150, and `PublicationBareParity.bare` provide actual source tag facts. Mu exposure must not be used as a bare-root tag.

The remaining constructor work is substantive. It must show that actual union flattening, duplicate removal, Empty removal, and ordinary-row merging preserve deletion observations up to `Equivalent`. It must also preserve the exact standalone tag after normalization. Existing `StoredProfileComposition.makeUnion` at line 311 proves the unfiltered profile law, not this deletion law. Node survival needs only actual retained rows and their strict-child assignment laws; dead source rows must not acquire new input requirements.

The chronological step must apply the stronger law to the exact selected stored record. It must use its exact depth and ordinary probes. It must prove the new candidate law from the actual current callbacks and the already established laws for nested publications. It must then handle `keepFirst` by retaining either the old proved record or the new proved candidate. `NativeBinderProfile.build_profile`, lines 29 onward, is an existing conditional consumer of a final payload heap. It is not that heap's producer.

## Scope and next proof obligation

The observer and actual singleton-filter bridge are appropriate foundations. The next source theorem should carry both live assignment compatibility and live cut compatibility, plus the existing aliases and exact tagged bare-root equality. Its binder case needs a chronological selected-writer law and the two finish cases above. No result here proves general source comparison, reader observation transport, recursive normalization completion, or correspondence with Haskell. No Haskell defect was identified.

## Source pins read

These hashes identify the bytes read. The two new root modules were still part of the current checkpoint work; this report does not freeze their later packaging.

| Source in `lean/MicroCFTA/` | SHA-256 |
| --- | --- |
| `SourceCurrentStoredRootDeletion.lean` | `888a0cd87de936db016b49801fc9cecac433516e508feec60bcaab6dfe2962a0` |
| `SourceCurrentStoredRootDeletionFilter.lean` | `9ad271bb102ba826a3807302b4c79b0b5bb256a98b115bcb61f649b4c59f3011` |
| `SourceCurrentScopedProfileInputs.lean` | `b3a65202196d541cd6d833faef290167f845a6e7674498d2fdb9c997a73cff30` |
| `SourceCurrentUsedBinderAliasTransport.lean` | `192ccb08a7322c3619781b3886ce491f0a4b72b2914e14d108212d9c29171d2e` |
| `SourceCurrentUsedBinderOutputTags.lean` | `249b06a358eac40de2451a591566f679ebb02d5be7edbd7432b9633e8b5a5d27` |
| `SourceCurrentNativeMuPublicationCallbacks.lean` | `fcf760e62065456344180f8edcc4495a784006c73d087d06d47ab0f2a26b0395` |
| `SourceCurrentNativeNormalizedComparison.lean` | `c432a1f0b1f984772c5f53c3a50456d84fe2d0a12f308f660785f25f752a9cb2` |
| `SourceCurrentNativeNormalizedComparisonExecution.lean` | `9d2f9e64c62396b76e32c76428369188fc09371c1b19e100f8c0ca79b80e1a00` |
| `SourceCurrentStoredMuUnusedProfile.lean` | `96e981b115952492e0d5f633b416d6e7a599cda38a673abe245dc7c81baf4354` |
| `SourceCurrentStoredProfileComposition.lean` | `e3d1f4c2bc788e65c52fcd07f1ba8bacb80b71931f39a393f588309ec1a5e695` |
| `SourceCurrentNativeBinderProfile.lean` | `89b5643f3f51e08c441ebc4e014243a24b73abac0efc1086678976c4dfd566e2` |
