# Causal Empty fusion route audit

Reviewed on 2026-10-18 at 20:54 CEST. This is a read-only design audit. The eventual producer is owned by root. No Lean run or production edit is made here.

The intended target is the exact old FilteredSourceFusion.Fusion interface plus History empty reader. All old historical Contexts, literal completed raw calls, Grows, Aliases, live self tests, paired resolved physical Empty flags, Ready, raw availability, actual reader filter equations, actual warm execute equations, and replacement availability remain explicit. No Heap Correct, BodyIH, full output relation, future completion, raw depth, BinderFree, or nonempty-replacement premise is added.

## Required adapter details

1. Derive reader payload facts through CausalHistoryProfiles.compare. Its History argument already removes the supplied old Correct heap. The source return Grows premises retain their original directions. Do not infer History at an earlier raw entry from this reader history.

2. For each actual replacement environment, use rho n = profile((env n).getD(reference n)) and rho0 n = if isEmpty(rho n) then some [] else none. Lexical Paired Empty does not imply equality of the unabstracted rho profiles. It does imply exact equality of the canonical rho0 profiles on live paired labels.

3. Apply SourceEmptyAbstraction.same_empty to the SAME stored encode/leaves plan to justify the denote projection. The deleted projection must follow ORIGINAL root unions and treat node/Mu as atomic denote calls. It must not delete a reference later exposed by a Mu or replacement. isEmpty equality is enough here; full Equivalent of actual rho and rho0 is generally false.

4. Fixed symbolic captures can themselves be references. Their Paired Slot then gives resolved Empty agreement, not literal environment equality. Fixed nonreference captures retain literal maps on their free names. Live support can select only those names needed by the source. Do not require all original lexical captures to be Available at reader.

5. Replacements reader env covers actual some values only. For env n = none, the fallback is a literal reference and its physical Empty flag is false directly. Do not infer availability of every fallback interned reference. Ready plus actual some replacement availability supplies profile/physical Empty reflection where needed.

6. Old Fusion filters at reader, NOT at the earlier source-return heap. Its raw availability and Ready reader give the Normal and Available premises for StoredRootDeletionConstruction.filter_profile at reader. No new historical build/filter adjacency or warm source replay premise is required.

7. The standalone-own exception is essential. UsedBinderOutputTags.bare derives raw own parity from actual historical source Contexts and the supplied self tests on FULL Scope, including the Depth anchor. In this branch the filter keeps the bare own reference and its assigned profile. An uncut comparison, plus Normal/Available uncut readback, compares its canonical assigned profiles. In the nonbare branch the singleton-cut comparison gives the needed deleted profile. Source-cut compatibility comes from the live part of the same self tests.

8. StoredProfileFunction.execute supplies actual result profile equivalence from the Ready entry, filtered availability, and Replacements. Filtered availability follows from the actual filter equation. Actual result availability follows from the compiled source execution; because the calls are warm, their returned state is the same reader. Then isEmpty_profile converts the final profile Empty equality to literal NodeRef.empty equality.

## Scope cautions

The new causal target does not repair or replace the refuted unrestricted arbitrary-cache Fusion contract. History supplies genuine prior callback provenance and derives the cache payload law. Ready alone does not do so. Historical source calls and replacement environments can remain arbitrary under the exact existing hypotheses, including arbitrary recursive captures and replacements which become Empty.

This result supplies physical row-survival agreement. It supplies no same-symbol/full-guard row relation, ordered child observations, used-Mu epsilon transfer, all-depth Same, recursive termination, or Haskell correspondence. A genuine source-generated Directed instance remains the deeper target.

## Stable input pins

| File | Bytes | SHA256 |
| --- | ---: | --- |
| `lean/MicroCFTA/SourceCurrentFilteredSourceFusion.lean` | 17912 | `5e660880a5466f1afc53d52ee762ce258aec5fcea0250c17b8f66cdd6508e441` |
| `lean/MicroCFTA/SourceCurrentCausalHistoryProfiles.lean` | 5545 | `78ac761edfd4a2575d92931f8b96488814d2bd1e15e29d103ecaf20c9017d8fc` |
| `lean/MicroCFTA/SourceCurrentCausalSourceRootLaw.lean` | 5418 | `8a7bbb27ce43d48f507508a990fe0dadf2ca42eeb1df3983047ef63cfcb1675b` |
| `lean/MicroCFTA/SourceCurrentCausalSourceComparison.lean` | 4699 | `1c56e9317225d392e27aad94f2f0d9ae4a49658f5c7d99009af046d14e831e8f` |
| `lean/MicroCFTA/SourceCurrentScopedProfileInputs.lean` | 12059 | `b3a65202196d541cd6d833faef290167f845a6e7674498d2fdb9c997a73cff30` |
| `lean/MicroCFTA/SourceCurrentScopedDeletionInputs.lean` | 7948 | `a3c80cce6ff2c3897f40c28e568caac48f42dca85153e2ca57897a5655c02c64` |
| `lean/MicroCFTA/SourceCurrentReaderReplacementSlots.lean` | 12506 | `ab29b32220b1d6a77db19cdbebb78c9cd98881fe4c6d82439fea9adfb15f6780` |
| `lean/MicroCFTA/SourceCurrentSourceEmptyAbstraction.lean` | 12635 | `2f2c46b72904bb0f374e25fb9b0c8b4febabe1f5eb222781346145c50153693f` |
| `lean/MicroCFTA/SourceCurrentStoredProfileFunction.lean` | 8323 | `7d6ebb0a59f62c42dda78a527dd339961f1c60d23bde5ddde7f6e411261b4e9c` |
| `lean/MicroCFTA/SourceCurrentStoredRootDeletion.lean` | 6695 | `888a0cd87de936db016b49801fc9cecac433516e508feec60bcaab6dfe2962a0` |
| `lean/MicroCFTA/SourceCurrentStoredRootDeletionConstruction.lean` | 11172 | `4f5ab3e64000ec9bb54cb95e17a03f5634fbe803eead98af89dcbd42c7c58de5` |
| `lean/MicroCFTA/SourceCurrentUsedBinderOutputTags.lean` | 29723 | `249b06a358eac40de2451a591566f679ebb02d5be7edbd7432b9633e8b5a5d27` |
| `lean/MicroCFTA/InternedRootProfileNode.lean` | 6477 | `941990a324cad726e43574706bc8eeaca874f0738b704d76315eccda00befa11` |
| `lean/MicroCFTA/InternedProfileComposition.lean` | 4375 | `27201e210f5f816d375d02e87fe463e869452680fb6b14784e212fa5b6e5f095` |
