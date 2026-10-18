# Independent audit of causal strong root contracts

Reviewed on 2026-10-18 at 20:43 CEST. Final production SHA256: `7267ccfd66fafb7b1dcd97810924d6bf4f1602a50eb4d3e6764182b7051baf45`.

No material semantic issue was found. The full 304-line source, its RootContract definition, the relevant filtering/tag/reflection helpers, and the direct-history dependency were read. No production file or frozen review was changed. No Lean process was run.

## Exact stronger contract

`StoredMuRootContract.Correct` combines two facts. First, all original root deletions agree under arbitrary outer profile assignments and one common local replacement profile. Each local name has tag none; external names retain their exact some(name) tag. Second, the exact standalone-reference tag agrees. An outer none from bare means that the value is not a standalone reference; some(none) identifies the standalone local reference. Thus the contract distinguishes a bare reference from an opaque Mu that later exposes that reference.

Cuts test ORIGINAL root references before profile assignment. They do not enter node children, Mu bodies, or references exposed by replacement/unfolding. The theorem does not silently replace this observation with a denotation-only equality.

## Candidate deletion proof

The private candidate producer recovers both actual raw source calls and filters. `raw_callbacks` supplies forward Grows from both raw return heaps to the exact event.afterBody reader. Initial/local Contexts, raw availability, and Normal at each actual raw heap are derived from actual callback execution and reservation. No later history is used backwards.

Actual ordinary and reserved freshness on live captures gives scoped profile and combined-cut compatibility. The same original source and capture list feed the existing conditional full source Law at event.afterBody. This call uses only the OLD assigned-profile heap at that reader.

The standalone OWN case is handled before erased filtering. `PublicationBareParity.bare` derives both bare-own cases together. Both sides then have the same tagged cut and common local assignment, including either choice of cuts none.

For the non-own-bare case, actual erased_filter adds the own singleton to the original raw cuts. Both actual filtered callbacks are already known not to be standalone own, so eraseSelf is the identity on those returned values. `combined_tag` is exact: away from own, tag is some(name); at own, the added own cut is true regardless of whether cuts none or cuts(some own) differs. This is why the final law can quantify arbitrary tagged cuts without assuming the desired filtered result. Opacity from Mu remains unchanged by these root cuts.

## Exact bare-tag proof

This part is independent of the assigned-profile comparison. Actual callback_profile plus the pure callback form derives matching literal profile opacity. `UsedBinderAliasTransport.publication_filtered` supplies both directions of actual free-name correspondence. Its NamePair distinguishes own renaming from identical external names. tagged_pair turns it into exact tagged-name correspondence.

For a standalone reference on one side, forward correspondence supplies a free name on the other. Opacity parity excludes an opaque result. pure_free identifies its pure root names. Backward correspondence plus injectivity of the OTHER side's tag makes that root profile a singleton. `profile_single_iff` uses Normal and Available to conclude an actual standalone reference; it excludes a hidden singleton union. The argument is symmetric. Therefore the contract proves every external bare tag as well as local bare parity, without assuming a whole output comparison or conflating Mu opacity with a reference.

## Chronological public producers

Public publication takes only the actual Publication and History empty event.afterBody. It derives the OLD payload heap with CausalHistoryProfiles.heap, then calls the private candidate with the already proved full source Law. It takes no supplied source law, old profile heap, or stronger RootContract heap. The dependency is old assigned-profile chronology first, stronger tagged contract second.

The private strong history_heap keeps the actual empty-table prefix. It obtains each callback heap in execution order. Reservation leaves nodeRecords unchanged. The body subtree yields the earlier strong heap. Only then does complete retain an existing exact winner or install the candidate proved by publication. Public heap discharges the initial invariant at empty tables. The candidate proof does not require its own stronger contract, so this second chronology is not circular. NoNewMu is sufficient in retain because this payload predicate is state independent.

## Scope and verification

This is a stronger original ROOT observation contract at actual causal payloads. It is not full guarded row equivalence, mutual ordered-child simulation, epsilon-language equality, general recursive termination, or Haskell correspondence. Arbitrary summary-valid or Ready caches still require their own causal history; the refuted unrestricted arbitrary-cache binder contract is not reinstated.

Selected strict direct4 is terminal-zero with a literal zero-byte log. Canonical2 is warning-free and reports 656 jobs. The existing full public1 group was independently rechecked by the hardened parser: two complete proof/axiom pairs, all eight printer options, standard-three axioms, no omissions or warning/error output. This review owns zero public or constructed pairs and reuses two public pairs.

## Input pins

| File | Bytes | SHA256 |
| --- | ---: | --- |
| `lean/MicroCFTA/SourceCurrentCausalPublicationRootContract.lean` | 19677 | `7267ccfd66fafb7b1dcd97810924d6bf4f1602a50eb4d3e6764182b7051baf45` |
| `lean/MicroCFTA/SourceCurrentStoredMuRootContract.lean` | 9131 | `6d0ab051177b85cd726a884a4b084b6a880084dc095bf3ee4f29197c6d641ec5` |
| `lean/MicroCFTA/SourceCurrentCausalHistoryProfiles.lean` | 5545 | `78ac761edfd4a2575d92931f8b96488814d2bd1e15e29d103ecaf20c9017d8fc` |
| `lean/MicroCFTA/SourceCurrentCausalSourceComparison.lean` | 4699 | `1c56e9317225d392e27aad94f2f0d9ae4a49658f5c7d99009af046d14e831e8f` |
| `lean/MicroCFTA/SourceCurrentCausalSourceRootLaw.lean` | 5418 | `8a7bbb27ce43d48f507508a990fe0dadf2ca42eeb1df3983047ef63cfcb1675b` |
| `lean/MicroCFTA/SourceCurrentCausalSourceBinderComparison.lean` | 19681 | `c35e272255adc514d7b8beb2bce6ac2f42a422495f4d3533a0c32f4e514d8e21` |
| `lean/MicroCFTA/SourceCurrentCausalPublicationProfile.lean` | 9832 | `ab2e17de3e8cb67c495a1ae01bcd9e4b180a3ae3bf3de1089ac1df1e595717df` |
| `lean/MicroCFTA/SourceCurrentPublicationHeapInduction.lean` | 6639 | `690392065b04a6b3e30a22279b058b8b88214d0ffa985e26d127f44ac3f6df9a` |
| `lean/MicroCFTA/SourceCurrentNativeMuPublication.lean` | 24007 | `e24184ee19ac4028a3e1604a82fc3cfea92f4b40d5a8490d08f02143b049efb2` |
| `lean/MicroCFTA/SourceCurrentNativeMuPublicationCallbacks.lean` | 6552 | `fcf760e62065456344180f8edcc4495a784006c73d087d06d47ab0f2a26b0395` |
| `lean/MicroCFTA/SourceCurrentScopedProfileInputs.lean` | 12059 | `b3a65202196d541cd6d833faef290167f845a6e7674498d2fdb9c997a73cff30` |
| `lean/MicroCFTA/SourceCurrentScopedDeletionInputs.lean` | 7948 | `a3c80cce6ff2c3897f40c28e568caac48f42dca85153e2ca57897a5655c02c64` |
| `lean/MicroCFTA/SourceCurrentStoredRootDeletion.lean` | 6695 | `888a0cd87de936db016b49801fc9cecac433516e508feec60bcaab6dfe2962a0` |
| `lean/MicroCFTA/SourceCurrentStoredRootDeletionErasure.lean` | 6256 | `17ad9906ada92e1b02cc640f2e4302dd7288bdd38a191980c79fe8db575f97c2` |
| `lean/MicroCFTA/SourceCurrentStoredRootDeletionConstruction.lean` | 11172 | `4f5ab3e64000ec9bb54cb95e17a03f5634fbe803eead98af89dcbd42c7c58de5` |
| `lean/MicroCFTA/SourceCurrentNativeNormalizationFreshness.lean` | 4330 | `8e7873d04f59305f43ef2f910ae08db1edfaed71cb69548adb30778126a76366` |
| `lean/MicroCFTA/SourceCurrentUsedBinderAliasTransport.lean` | 26779 | `192ccb08a7322c3619781b3886ce491f0a4b72b2914e14d108212d9c29171d2e` |
| `lean/MicroCFTA/SourceCurrentPublicationBareParity.lean` | 7953 | `90e582014a0cf18fbb14ebdee55d508b61e7d8ea95d91c51b6d8aeb96cfb18e3` |
| `lean/MicroCFTA/SourceCurrentStoredMuProfileContract.lean` | 4689 | `278c5d9942df52bc6ec7b9ac3d28b430340d3c8cf20050ae2a8f6d0fd00c9040` |
| `lean/MicroCFTA/InternedRootProfileReflection.lean` | 5194 | `537dc8f26eced40b7423f798cc97794b0d88a9c6b6169bd86bfe1e420b0b2982` |
| `lean/MicroCFTA/InternedProfileCallbackForm.lean` | 4803 | `1935cccafd19b457b4e5ce69f47dbafbc0a04a4785714c6ce25016dcac911e69` |
| `lean/MicroCFTA/InternedFilterSelfReference.lean` | 5637 | `e5a54fe8dcf33b9263a94e053b412fcd753d5d53a999dbbe73d0f0f082786377` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-root-publication-direct-4.json` | 835 | `5024ac6b6b0d5845cb1a316fb376b67cf3bb02f188c41f7a7bebec227e154c31` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-root-publication-direct-4.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-root-publication-direct-4.limits.json` | 90 | `408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-root-publication-canonical-2.json` | 663 | `5e8eab4642fbd4a17ff82382a9fd20dd569ec3bfb40efda6d0633ea9c43d658f` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-root-publication-canonical-2.log` | 122 | `bb0b38dd41d2fee5125ef75b83247cb89f0dde6abf6d82e92893a3a961c960cc` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-root-publication-canonical-2.limits.json` | 90 | `408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-root-publication-public-1.json` | 835 | `039d1a9e38a9fcd3c7618bcba753717298f5fbd4aa620547d881ec4e6bb7a6de` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-root-publication-public-1.log` | 4534 | `546d34f440a46dd1656136cee7ac580f5b2586f394b816c2e855076eee76de75` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-root-publication-public-1.limits.json` | 90 | `408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-root-publication-direct-4.source.lean` | 19677 | `7267ccfd66fafb7b1dcd97810924d6bf4f1602a50eb4d3e6764182b7051baf45` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-root-publication-public-1.source.lean` | 788 | `cfea6a4758db14266bd3a7a8f478e689f1a86830649f03876e7dae2f5176b1ea` |
