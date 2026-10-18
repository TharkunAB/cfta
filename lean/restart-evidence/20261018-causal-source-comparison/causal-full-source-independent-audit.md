# Independent audit of complete causal source root comparison

Reviewed on 2026-10-18 at 20:35 CEST. The final source is `SourceCurrentCausalSourceComparison.lean`, SHA256 `1c56e9317225d392e27aad94f2f0d9ae4a49658f5c7d99009af046d14e831e8f`.

No material semantic defect was found. This review makes no production changes and runs no Lean build. The main proof and all source, publication, context, selected-winner, filtering, and chronology contracts below were read from the pinned source. The node, union, binder, and publication proof bodies were inspected.

## Non-circular proof order

`CausalSourceRootLaw.Law` is conditional. Its reader supplies `Heap StoredMuProfileContract.Correct`, actual `History empty reader`, and forward `Grows` from both completed source returns. Each entry supplies its own historical `Context`. The law also requires exact live aliases, profile compatibility, root-cut compatibility, and the two literal successful source equations. It does not supply the desired parent comparison as a premise.

`CausalSourceComparison.source` proves this conditional law for every syntax form by strong induction on `sizeOf` the ORIGINAL syntax. Union induction uses original member membership. Node induction uses an original row and its original child membership. Binder induction uses the strict original body. No measure of a returned value, generated callback result, stored winner body, or current Mu depth is used.

`CausalPublicationProfile.publication` applies that completed syntax theorem at `event.afterBody`. `raw_callbacks` supplies the actual raw ordinary and reserved-body calls and FORWARD growth from each raw return to this exact pre-installation reader. The reader payload heap and empty-table history are explicit earlier facts. They are not inferred from the candidate being proved. Both local references are available at their actual entries. The reserved local is available after its actual reservation.

`CausalPublicationHeapInduction.path_heap` is the second, independent induction. For a publication, the Depth path first gives its prefix and heap. The ordinary path then gives its prefix and heap. Reservation changes `nodes` but leaves `nodeRecords` unchanged. The body path gives its prefix and heap. Only then does the publication obligation prove the candidate. `PublicationHeapInduction.complete` retains a previous exact winner or installs this proved candidate. Thus the candidate is not included in its own invariant obligation. A completed nested publication can already occupy the key; it is an earlier callback-path result, not an assumed current candidate.

This remains valid for smart-unused results. The proof establishes a property of every installed Mu payload even when cleanup returns a value of depth zero. It does not compare candidate depth with the smart return depth. Both complete and pending stopping states are covered by the actual issued-history producer.

## Complete source coverage

Empty and variable cases derive their result from literal source equations. Out-of-range variables return Empty. Fixed captures use actual availability plus free-name congruence. Varying slots use their scoped profile and cut agreements. Unused lexical inputs impose no result comparison obligation.

The node case follows the actual ordered row and child schedules. It derives callback-entry contexts from the executions and uses completed tails plus actual constructor growth to reach the common reader. An original live row inherits only its live child aliases and profile agreements. An original dead row has an actual Empty child under both input maps; that child stays Empty under arbitrary assigned profiles. Therefore dead rows need no unjustified child agreement. Normal-only `makeNode` profile construction gives the final formula. This observation deliberately ignores the node symbol and guard while using the actual child-survival conditions.

The union case retains each original adjacent member call. It derives tail growth, entry contexts, and all member agreements from original membership. It combines the member induction results and the actual Normal-only makeUnion deletion law over the ORIGINAL member lists. Flattening, duplicate removal, and canonical ordering do not require a future warm subgroup call or an assumed reader-wide lexical availability fact.

The binder case derives the same actual local-use decision from the two current probe pairs. Actual Depth callbacks make the repaired ordinary names fresh on live source scope, including the Depth anchor. This derives the body aliases and the extended profile/cut conditions. The retained branch applies the strict-body law with singleton local cuts. Exact source output tags provide bare-local parity; the Normal-only filter formula handles the standalone-self exception. A common finite fresh marker gives both selected stored-body reductions. Actual free-name support derives equal closed/open decisions. Original root cuts do not descend into a retained Mu or into replacement-exposed references.

The unused branch obtains exact current ordinary readback from actual history at the later reader. `NativeUnusedRootShadow` derives local-profile independence and an Empty local assignment. The strict-body law uses the original cuts combined with the local singleton cut. The reader has no Ready, Normal, or issued-set premise. The proof never requires History at an earlier point by reversing a later history.

## Actual candidate contract

The target `Correct` quantifies every outer profile assignment and every common local profile. It compares denotation of the selected stored body with denotation of the ordinary probe under their exact own-reference shadows. It is state independent. Its full assigned-profile equality is not one of the initial Context fields.

For a publication, both calls use the SAME source expression and captured values. Actual reservation and the actual Depth probe provide distinct local freshness from live captures. Scoped profile extension, scoped local cuts, and publication alias facts therefore meet the source law. Actual filter_self_iff and PublicationBareParity establish equal bare-self cases. Both actual filter profiles then yield the complete universally quantified candidate contract. This proves the real candidate, not a guessed current or earlier source writer.

The retained-request adapter recovers the actual table winner and identifies its complete current probes by resident reference identity. Forward nodeRecords growth reads that same stored body at the reader. It does not identify the earlier writer syntax with the current requester syntax.

## Initial assumptions and exact scope

A generic historical Context contains Normal, available lexical inputs, the earlier literal root-profile heap, the free-name heap, and the decoded depth/deep-name heap. These are substantial semantic assumptions, not weak physical Good. They are not the new universally assigned `StoredMuProfileContract.Correct`. Their existing preservation and empty-context producers are used explicitly. The generic `build_heap` also retains its stated initial Correct heap and actual empty-table prefix.

`closed_heap` discharges all of these entry obligations at the actual empty tables and empty lexical environment. `constructed_heap` then rewrites a literal completed closed build. Therefore the new Correct heap for arbitrary closed SOURCE syntax is derived, not assumed. This statement does not cover arbitrary prepopulated caches merely because they satisfy Ready or weak validity. Artificial Ready caches from the earlier boundary remain outside this closed causal construction claim.

The result is equivalence of assigned ROOT profiles and original root deletion observations. Profile equivalence preserves opacity and root-name membership, not list multiplicity or ordering. It is not an all-depth row, guard, epsilon-language, or finite-tree-language equivalence. In particular an ordinary node and another ordinary node can have the same root profile while their symbols or guards differ. No claim of general outer recursive termination, active-node exclusion, arbitrary native intersection correctness, or Haskell API correspondence follows from these theorems alone.

## Evidence and counts

The pinned final direct check has exit code zero and a literal zero-byte log. The pinned canonical check is warning-free and reports 653 jobs. No additional build, public probe, or constructed example is owned by this audit. Root's later full public and Audit receipts remain outside these pins until selected by their owner.

## Input pins

Each row pins the complete file bytes by repository-relative path and SHA256. The source pins are independent of mutable root package metadata or fixtures.

| File | Bytes | SHA256 |
| --- | ---: | --- |
| `lean/MicroCFTA/SourceCurrentCausalSourceComparison.lean` | 4699 | `1c56e9317225d392e27aad94f2f0d9ae4a49658f5c7d99009af046d14e831e8f` |
| `lean/MicroCFTA/SourceCurrentCausalSourceRootLaw.lean` | 5418 | `8a7bbb27ce43d48f507508a990fe0dadf2ca42eeb1df3983047ef63cfcb1675b` |
| `lean/MicroCFTA/SourceCurrentCausalSourceNodeComparison.lean` | 22328 | `2d7dd361a4a4599bae78bd835797ff2db9a2922d4b2c52c1f9c663e366921498` |
| `lean/MicroCFTA/SourceCurrentCausalSourceUnionComparison.lean` | 11511 | `cc2022979567c612e79231d84fb922ca1519c2e0d4b96ab6bc2b8f285f1cd1b5` |
| `lean/MicroCFTA/SourceCurrentCausalSourceBinderComparison.lean` | 19681 | `c35e272255adc514d7b8beb2bce6ac2f42a422495f4d3533a0c32f4e514d8e21` |
| `lean/MicroCFTA/SourceCurrentCausalPublicationProfile.lean` | 9832 | `ab2e17de3e8cb67c495a1ae01bcd9e4b180a3ae3bf3de1089ac1df1e595717df` |
| `lean/MicroCFTA/SourceCurrentCausalPublicationHeapInduction.lean` | 5160 | `038c9e9b5b2e7b47c45bf578a5ec2f7e8aa98285a999a893e81fe6e99bfdfe4b` |
| `lean/MicroCFTA/SourceCurrentPublicationHeapInduction.lean` | 6639 | `690392065b04a6b3e30a22279b058b8b88214d0ffa985e26d127f44ac3f6df9a` |
| `lean/MicroCFTA/SourceCurrentNativeRetainedRootDeletion.lean` | 6557 | `51f5ace967a1ffdd4018f37ae632483f89fffe0f78806a7a2f65318e537c9019` |
| `lean/MicroCFTA/SourceCurrentNativeUnusedRootShadow.lean` | 6153 | `133f5a485eaff91908f60ad958f8a2ccf1e4e13c5e2a52d52b910bc4cae6f60e` |
| `lean/MicroCFTA/SourceCurrentScopedProfileInputs.lean` | 12059 | `b3a65202196d541cd6d833faef290167f845a6e7674498d2fdb9c997a73cff30` |
| `lean/MicroCFTA/SourceCurrentScopedDeletionInputs.lean` | 7948 | `a3c80cce6ff2c3897f40c28e568caac48f42dca85153e2ca57897a5655c02c64` |
| `lean/MicroCFTA/SourceCurrentStoredMuProfileContract.lean` | 4689 | `278c5d9942df52bc6ec7b9ac3d28b430340d3c8cf20050ae2a8f6d0fd00c9040` |
| `lean/MicroCFTA/SourceCurrentStoredMuFinishProfile.lean` | 5560 | `1a1984bf580ec36707b3358255a4d783943a9714b89eec9ab460e388b637764a` |
| `lean/MicroCFTA/SourceCurrentStoredMuProfileReduction.lean` | 9142 | `2e63b1f530791ad85bf8f3a943f00d866c603d6585eae2f4a5ca52794aa310f9` |
| `lean/MicroCFTA/SourceCurrentStoredMuTrackedProfile.lean` | 12052 | `a523e6d07c746744bbb800806f681c17ff77ef1ef35213cc8201470debd84812` |
| `lean/MicroCFTA/SourceCurrentStoredRootDeletion.lean` | 6695 | `888a0cd87de936db016b49801fc9cecac433516e508feec60bcaab6dfe2962a0` |
| `lean/MicroCFTA/SourceCurrentStoredRootDeletionConstruction.lean` | 11172 | `4f5ab3e64000ec9bb54cb95e17a03f5634fbe803eead98af89dcbd42c7c58de5` |
| `lean/MicroCFTA/SourceCurrentStoredRootDeletionErasure.lean` | 6256 | `17ad9906ada92e1b02cc640f2e4302dd7288bdd38a191980c79fe8db575f97c2` |
| `lean/MicroCFTA/SourceCurrentStoredProfileNormalConstruction.lean` | 11601 | `686af7d4a3626320d6b3819209817a153e84d9f19630b3d2b0769033623e3509` |
| `lean/MicroCFTA/SourceCurrentProfileFold.lean` | 3639 | `fc30d562677529042c2e3af7d7a681f804f738d0155760f86f95fc4bc895d864` |
| `lean/MicroCFTA/SourceCurrentNativeReaderUnusedRootDeletion.lean` | 4261 | `55f47444053bf906448648c3f632514f9d2b007b7324c6c1be4acd239f4d43c9` |
| `lean/MicroCFTA/SourceCurrentNativeBinderExecution.lean` | 6826 | `52800a69fd008c7eaa8c4ccaeaf5b1534792dfbe741b3958e3789fe3a447f3e7` |
| `lean/MicroCFTA/SourceCurrentNativeRequestWinner.lean` | 2526 | `2e6d9e5e5bb68ed86501e9f995c97befb878eef12f1dc04ec740bd6d3debdac6` |
| `lean/MicroCFTA/SourceCurrentNativeNormalizationInputs.lean` | 7127 | `fdc8f1c7bb408770dc17a25e5fd16c2201da4ddf8f9e51a4ef971960ac21840b` |
| `lean/MicroCFTA/SourceCurrentNativeNormalizationFreshness.lean` | 4330 | `8e7873d04f59305f43ef2f910ae08db1edfaed71cb69548adb30778126a76366` |
| `lean/MicroCFTA/SourceCurrentNativeNormalizedComparison.lean` | 27260 | `c432a1f0b1f984772c5f53c3a50456d84fe2d0a12f308f660785f25f752a9cb2` |
| `lean/MicroCFTA/SourceCurrentUsedBinderAliasTransport.lean` | 26779 | `192ccb08a7322c3619781b3886ce491f0a4b72b2914e14d108212d9c29171d2e` |
| `lean/MicroCFTA/SourceCurrentUsedBinderOutputTags.lean` | 29723 | `249b06a358eac40de2451a591566f679ebb02d5be7edbd7432b9633e8b5a5d27` |
| `lean/MicroCFTA/SourceCurrentPublicationBareParity.lean` | 7953 | `90e582014a0cf18fbb14ebdee55d508b61e7d8ea95d91c51b6d8aeb96cfb18e3` |
| `lean/MicroCFTA/SourceCurrentNativeMuPublication.lean` | 24007 | `e24184ee19ac4028a3e1604a82fc3cfea92f4b40d5a8490d08f02143b049efb2` |
| `lean/MicroCFTA/SourceCurrentNativeMuPublicationCallbacks.lean` | 6552 | `fcf760e62065456344180f8edcc4495a784006c73d087d06d47ab0f2a26b0395` |
| `lean/MicroCFTA/SourceCurrentNativeMuIssuedHistory.lean` | 14612 | `1d3d4fcd733ed325287bbfb288b70df88476b3989657b056dd3819abf4079563` |
| `lean/MicroCFTA/SourceCurrentNativeMuGrowthHistory.lean` | 3187 | `98c08f9029a262a632d56d67e3038aadecccd9b5aa4fa112dd8bde3b132a9c0a` |
| `lean/MicroCFTA/SourceCurrentNativeNormalizedComparisonExecution.lean` | 31464 | `9d2f9e64c62396b76e32c76428369188fc09371c1b19e100f8c0ca79b80e1a00` |
| `lean/MicroCFTA/SourceCurrentConstrainedCapSourceHistory.lean` | 15587 | `123cae4b1815144531954e1e2ed246963f0325d54a06a5039d09694326e4a315` |
| `lean/MicroCFTA/InternedFreshOrdinaryContext.lean` | 6811 | `6c2ff37408657b29214e0f48ab680e88dcf314ffcb6d22b0738e76df35a2ad01` |
| `lean/MicroCFTA/InternedFreshOrdinaryDepthHeap.lean` | 8302 | `0b2621350645342b82f49c193643bd36b40ae393cdea109eadec53338ec42783` |
| `lean/MicroCFTA/InternedFreshOrdinaryProfileHeap.lean` | 4340 | `2e2c758dfcdc000ee63e0f5f912e9f726a4689b6664621e1cd6959ad89768498` |
| `lean/MicroCFTA/InternedFreshOrdinaryFreeHeap.lean` | 3958 | `37bc39986aaa1aae03761e7b9487e1f013768782644e089d3813e2356c25b7cb` |
| `lean/MicroCFTA/InternedFilterSelfReference.lean` | 5637 | `e5a54fe8dcf33b9263a94e053b412fcd753d5d53a999dbbe73d0f0f082786377` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-source-strict-1.json` | 776 | `74f90e9345e9e42f2475350ad2bd67b2460b0619fd60876e5a14369fd70e8c6b` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-source-strict-1.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-source-strict-1.limits.json` | 90 | `408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-source-canonical-1.json` | 617 | `ee1b5b48d7f31f920ab26d90d4f1c37a93f8ed7c5d15bc7010a434dcac2ecfcb` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-source-canonical-1.log` | 115 | `7fcd4cb678cdc517e795b12696e633923ae117ebfd9c5a46f13bbadff6a66886` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-source-canonical-1.limits.json` | 90 | `408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-source-strict-1.source.lean` | 4699 | `1c56e9317225d392e27aad94f2f0d9ae4a49658f5c7d99009af046d14e831e8f` |
