# Fold invariant source review

Timestamp: 2026-10-24 23:22:16 CEST. Verdict: CLEAR for the proposed three-theorem state-preservation scope. This is a source/API review. No declaration, proof, compiler, program, Git, or repository edit was performed.

`assimilated_preserves` has a direct route. The two actual pending-slot equations and `StorageValid.values` give the suspended-reference bounds. Concatenation preserves those bounds. Two applications of `set_storage` preserve storage after target replacement and source elimination. The ancestry update changes no storage field. `EnumerationCanonicalWaiting.assimilation_correct` gives unchanged canonical counts from the literal concatenated references. Its root function can be arbitrary and fixed; no union-find root or native heap premise is required. Distinct target/source is necessary: otherwise elimination overwrites the replacement. The existing Graph-based `assimilation_storage` is not the route for this checked native result.

`dispatch_preserves` can inspect the actual dispatcher and selected action at any finite native/worker bounds. Equal IDs and eliminated sources select a no-op. Missing slots and codecs select no action. Malformed pending shapes select an error action. Optional-node actions either reject `some 0` or perform the same literal assimilation. A completed checked query selects `Assimilation.finish` only after the actual worker branch and encoding; Empty rejects before writes, and other Values perform the same assimilation. Native/worker failures select no successful enum action. Therefore a selected action's observed successful singleton requires only the initial storage/count invariants. Context, ranges, Ready, native result meaning and completion are unnecessary for this state-only conclusion.

The action must execute at the SAME `before` used for dispatch. It captures suspended lists from that state. Execution at an arbitrary second state would not preserve its allocation bounds. The selected-action equation and actual raw singleton are concrete observations, not a callback output law. The proposed Root header states this condition explicitly.

`run_preserves` follows by induction on the original source list while generalizing the actual Caller, enum state and queries. Fold dispatches and executes each reached action once. It recurses only on the exact successful singleton. All other raw lists, native errors and missing actions return the current state in the outer endpoint field. The dispatcher theorem supplies the recursive invariants. This includes rejection, raw errors and unexpected multiple rows without dropping them. It does not assert that any fold completes.

The fixed external waiting map and root function stay unchanged. This proves no native count/index extraction, gained-only update, Safe, LiveRoots, global memo law, future range admission or full terminal/driver language result. The existing successful completion witness can later use this invariant theorem without a duplicate completion packet.

Root-selected header input: `/tmp/mcfta-pruning-enumeration-fold-invariants-20261024-root-public-headers.txt`, SHA-256 `db0986447ff3a07ada464d12a959a6639960b64f84e8caf44bb970371cb5a429`.

Cut hashes use the original bytes for the inclusive line ranges.

| Source | Whole SHA-256 | Cut | Cut SHA-256 |
|---|---|---|---|
| `lean/MicroCFTA/SourcePruningEnumerationDispatch.lean` | `fb2dcd0c1c5ba5abee27afeda86cb676682590f232b9c24ac75a759f843e970d` | 21–91 | `8d9a93d639aa1b1470aa0cb221e92d678a9426bd6b9d176ba47bd551249348f9` |
| `lean/MicroCFTA/SourcePruningEnumerationAssimilation.lean` | `cd4687d427310fa9999c9c47a1efe145866cc0bc8c25dc11950e6b02ea77c822` | 22–36 | `5803484e831af4350bf2ae31aa5fd4f7fb3a46c600aca5894f32d84d6f45082c` |
| `lean/MicroCFTA/SourcePruningEnumerationFold.lean` | `0a5ae94315af7024fc4cc80bcc00163996fceaf95568969df73401fea9c2db16` | 17–43 | `e927266edcd5052ec009a6774652a25a1fe2d37436be2c073ec225ed0c334f51` |
| `lean/MicroCFTA/EnumerationCorrectness.lean` | `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d` | 276–282 | `d784ea9664a90a66cfbe58fffc602a646d86b70776265e73ec00314248e457bf` |
| `lean/MicroCFTA/EnumerationCorrectness.lean` | `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d` | 631–649 | `bf698014eb5fde84ecc98bcf796e83e47ee1e44474203b119d0715e49a46b129` |
| `lean/MicroCFTA/EnumerationCorrectness.lean` | `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d` | 959–981 | `9595bb0a68a45778fc72a5f9fcb81cd96e438d8dfbb1390fa3be0fa0e55bc30b` |
| `lean/MicroCFTA/EnumerationCanonicalWaiting.lean` | `a941b9b49e87115f26ecba015bc23e15a3d873410ac943ded77ff5f8963057bd` | 243–274 | `d81cda2be51f88bbdc6964420934e732c1602ec6bd79a7e0dd5c270c06c0ee91` |
| `lean/MicroCFTA/EnumerationSchedule.lean` | `3e84f2059725b3c0392d4df005574fde2918290cb393c4be0d549a62ad4a4e45` | 201–205 | `be8067d0c23937679c300143e382827a283f39018cff11ad4c602915c9566d8b` |
| `cfta/src/Data/CFTA/Enumeration.hs` | `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` | 490–509 | `08e5dbf6a96b2d8df51a8a52154bab51984f49a00946a636737512bccaed6e3a` |
