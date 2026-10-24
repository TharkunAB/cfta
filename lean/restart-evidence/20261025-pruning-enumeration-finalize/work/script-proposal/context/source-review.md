# Captured-slot finalization: source review

Final source-only route review at 2026-10-25 01:10:56 CEST.

CLEAR for Root-selected V2 finish/run/complete, one local List Monad header and one typed reset-let header. Exact frozen owner inventory remains a separate gate. Native enumerateOutUVarWith captures uv′ before expansion, then clears expansionAncestry and calls setUVarValue at that same raw address. That operation reads the CURRENT old slot and removes its current references. No second representative/winner lookup belongs in this suffix. The address can differ from Terminal's returned hole winner.

The selected interface permits every present old UVarValue: pending Some/None, eliminated or enumerated. It removes references old, not pre-expansion scs. New enumerated fragment has no suspended references and candidate=false without decoding. NativeIndex.write already supplies the actual lost-before-gained update; count_complete derives one finite bound at the same unchanged forest for all waiting/change inputs. With gained=[], canonical replace_correct yields exactly count roots(-1)(references old), including duplicate occurrences. No new count identity, Graph equality or callback/result law is needed.

finish forces the current raw read between reset and write and derives the exact raw fragment/state singleton. run resets via existing Cached.frame, reads that same raw slot and computes the cached write. complete starts from the actual stored equation, genuine root/count/flag views, StorageValid, FragmentBound and PendingRealized. It derives finite run success and raw finish success; neither is an input premise. The stored equation supplies the allocated target bound. Missing raw storage is outside this certificate: cached run is partial and finish uses existing model rawValue failure; neither is advertised as a native Haskell Nothing/rejection/error behavior.

set_storage needs precisely the supplied bounded fragment. Resetting expansion ancestry changes no storage field. The existing list-set old/fresh argument preserves PendingRealized: retained pending payloads use the prior realization, while the fresh enumerated payload cannot be pending. No Coherent/Ready/IsRoot/Safe/LiveRoots premise is needed. Exact core equality preserves forest, counter, obligations and recursionAncestry, clears expansionAncestry and updates only the captured raw slot. No full Frame crosses that write.

This component takes the already returned fragment as data; it does not produce the preceding expansion or install at a newly selected winner. Earlier Mu/Union transformations, initial/allocated native flag history, full caller/cache history and selector integration, native maps/IDs/machine class bounds, flags/partition, Safe/LiveRoots, initial-only ranges and complete-driver/H6 obligations remain separate. No Haskell bug is claimed. Selected soft140–220/hard320 is a source estimate, not compiler evidence. I executed no program, parser, compiler or Git command and authored no mathematical body.

Selected V2 input identities:

- complete-header.lean.txt: `f78b0797bb874a248c0a516672a60a7344cf85c160e6c6b3ba2247231b7bc145`.
- context.lean.txt: `c0fab67a00fe714e1264fda4b9b62cd293ba5a634cdb9a80df21ecbe53243414`.
- definition-reset-header.lean.txt: `4b41df57f7431b62e7bfe15985ba5ea8d564663f45f415d91b3ff16a4b8ae7a1`.
- finish-header.lean.txt: `cc48bc9a0b5c0a1da5f3fc4fc34045ab169f1f804c503d7f10e1fdc9f8923920`.
- instance-header.lean.txt: `8793e67b6e81021c80ba21e3d41918fc2b6b1a181f787f2effe156190cbbda59`.
- run-header.lean.txt: `f5a4b2b0f7841b8776383ca3a54ca2e83767b262a70d82b09ef28f8877f25272`.
- design.md: `517c72f0785cf11337dba84334a3ccd13d28de0e04fca3d1f5e4eb7da4480014`.
- source-cuts.md: `dd536f74db17616bec84a3c052791095a4d1f685ca1b341ab00558a7df576aa0`.

Whole-source and exact inclusive cut identities:

| Source | Whole SHA-256 | Cuts and cut SHA-256 |
|---|---|---|
| `/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Enumeration.hs` | `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` | 432–474: `905e48b49029bc777011be390ca7e922bdbedaa7442dee2528300409bee4e518`, 879–903: `20418fab47b43ab4934a5013890c4aff1fef911cee1c9add7d2171edc168beb9` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationNativeIndex.lean` | `13c8b37a63e950f4b26d2e9c927cc3108b50b3024b96b3be70a8a539f6f7f160` | 16–51: `769cf1a59b10332a4f0711e5eb2bcb88c91d2ba3c64cb86b86e5adffffa20fe3`, 54–76: `b83e6b3791d84d2069b4e09852a3f37641c7e198e26a59e3742c2a741eafda42` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationCanonicalWaiting.lean` | `a941b9b49e87115f26ecba015bc23e15a3d873410ac943ded77ff5f8963057bd` | 24–37: `31052b9b62a5220816ef459605d975290a8f5be5732731f0ce2903f6dcb4696f`, 83–90: `18e7d356278dea527ab3a27093e6040b09c9c126acb09160cd8ae0f3d9ca525d` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationCorrectness.lean` | `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d` | 620–649: `bdf77b6ef928b0d7191855e35fc19ea6ec2da7db0eeeba73b817fc65dc698ad5`, 959–966: `5d1df1b2bbc39ce102fe5ca4eed735746ec4e135ee29374872d261cde1f39331` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationObservation.lean` | `5a7b858adc4febb75621b9836053f308924c22d5fd7662741da61cbdab629bf4` | 19–26: `e2c14f6c8055a017bf2a1980bee54ea9ee02a05770c0a93bda80ce0b3a86f016`, 45–54: `a6c5473363ae18efdd92de2be2d2e3cca6a1e8b4d46e642cd08be51836c461c7` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationWrites.lean` | `32864f9158615ee7787c7490356471489978a5622ea984d904f7b03329510a7e` | 60–67: `53376ceed0688fb37df82563adbd4f27d3cf835acb2ab352b432783b578fabed` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationState.lean` | `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4` | 67–73: `00f4bfb4dbaa1c2971dc5d8e325a63d07c4aaea3ddaf1e5909e8403de3c7682d`, 102–110: `7ccd7f27833581a40bce22c355559a255b01ee420be9b37d91a03023dd13f0ed` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationSchedule.lean` | `3e84f2059725b3c0392d4df005574fde2918290cb393c4be0d549a62ad4a4e45` | 36–38: `2cd429d8bd01728b451ff5d38c615eef6119a81a6ae6a6e50cac701e84e76c13`, 201–204: `12c743ccde9c625028b1e2bf1933e00d73f9ef5055e7f4ce8d19b3d026c1cac5` |
