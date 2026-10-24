# Terminal-prefix source feasibility

2026-10-24T21:41:22+02:00. FINAL — CLEAR for the bounded design; exact declarations remain pending.

Use existing EnumerateM with the standard product result `(List Nat × Nat × EnumerationWaitingIndex.Waiting)`. Initial waiting is an explicit external input. Waiting is `Nat → Option Int`; core EnumerationState has no waiting field. This preserves the real state and adds no carrier, Graph or shared monad. No Caller/Memos argument is needed merely to claim they remain unchanged: this operation does not execute native queries.

Follow native716–747 exactly: scan every ORIGINAL suspended variable; union the first ORIGINAL variable with each remaining ORIGINAL variable; resolve that first variable again; compute the distinct nonwinner keys; transfer those buckets. Return recorded order and duplicates unchanged. Do not union recorded roots or deduplicate the list supplied later to assimilation.

Reuse BuilderCaches.canonicalIds on the recorded list filtered against the winner. Existing member/nodup/sorted lemmas give ascending mathematical keys. CanonicalWaiting.moveMany_correct works for any list; redirect_fold_eq needs only derived key membership to identify the actual merged-root function. This proves canonical count correctness, not arbitrary literal native-container extraction. CanonicalIds avoids needing a new permutation/commutation theorem. Keep Int width/overflow and host IntSet/IntMap correspondence explicit.

The honest initial count premise is Correct roots before.values waiting together with actual Roots before.representatives roots. Neither Safe nor Context constrains an external waiting map. Initial Safe, bounded suspended references and InputsPending derive pending old representatives through inputs_pendingAt. Where inputs come from a real stored pending payload, pending_inputs supplies avoidance from PendingReferences. No supplied pending winner, desired output, key law or successful prefix is needed.

Existing representative/union and mapM/forM termination construct the three finite observations from totality. Schedule identifies the actual scan, union classes and winner afterward. Common bounds combine by addition and existing moreFuel retention; retain identical intermediate/final states. Completeness already constructs this prefix within its stronger Graph theorem. Reuse that route, without importing its intersection-law or satisfying-assignment premises.

Values and every nonforest field remain identical: counter, obligations and both ancestry fields included. Thus PendingRealized transfers for the SAME external heap, and recorded slots remain pending; winner membership derives the pending target. Actual final Roots and canonical waiting correctness are useful endpoints. Safe/LiveRoots are invalid in general before losing slots are eliminated. Compression Frame is also invalid across class-changing unions.

One action and one finite producer should fit roughly200–280 ordinary lines, subject to exact-header review. A named local List Monad may be needed; no new Symbol equality requirement is justified by these primitives. Incoming-node merge, later range admission/caller-safety composition, native flags/index extraction and full terminal/driver/H6 remain open. No bodies, compiler/parser, selected scripts or repository changes were made.

The following live pins use repository-relative paths under `/home/tritlo/Code/mcfta`. Cut digests concatenate the listed inclusive LF ranges in order without added bytes.

| Source | Whole bytes | Whole SHA256 | Cuts | Cut bytes | Cut SHA256 |
|---|---:|---|---|---:|---|
| `cfta/src/Data/CFTA/Enumeration.hs` | 71269 | `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` | 716-747 | 1862 | `b7deb0738f7ece02d39f3b3eeba7872461920b1ab851e879a11fc75b172d59cc` |
| `lean/MicroCFTA/EnumerationState.lean` | 33489 | `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4` | 66-80,113-119,190-194 | 1190 | `68c4ab8314fe6f3d8ec9fce1e29cf4f038912408bd079c4dab87d276323a60ce` |
| `lean/MicroCFTA/EnumerationExecution.lean` | 30176 | `b81e03600e03085ec32fc8c85026ca4af562593764b28d6f8dd776eb3ac98346` | 99-119,371-428 | 5609 | `5f55847f5b4e1249fdf962f88123374f12d3e2117b3e714c99ba68b20c4cb1bf` |
| `lean/MicroCFTA/EnumerationSchedule.lean` | 86287 | `3e84f2059725b3c0392d4df005574fde2918290cb393c4be0d549a62ad4a4e45` | 36-75,220-228,272-278,476-547,550-578,728-740,1111-1112 | 10939 | `05eb458d659e0974065bcdb9733d72db2d1f1c43dcb4e11ff3d42bf1e04befb3` |
| `lean/MicroCFTA/EnumerationCompleteness.lean` | 23285 | `1cafd52affc702de54e22a37e4ac12496d860b964c0628d95eb94f015fbf34f7` | 117-132,168-215,231-246 | 6896 | `ace3e8c0068f171c8b2db1f0aab9aba708ff661d0fe350477ff4001761bae25e` |
| `lean/MicroCFTA/EnumerationCanonicalUnion.lean` | 9776 | `b76617ea7f0fb0ba74b78125f9c2232302e7513d378ddbfa8deef0fea9cf8bd6` | 20-65,69-84,127-155 | 5756 | `cedd723f9195f6c50db4e050ef732d9248009eba0d6b473ee07be217399e442b` |
| `lean/MicroCFTA/EnumerationCanonicalWaiting.lean` | 14833 | `a941b9b49e87115f26ecba015bc23e15a3d873410ac943ded77ff5f8963057bd` | 35-60,173-180,230-241 | 2498 | `93b84086a167b1e3578dc2df23d572c895efcd862cb40a450a5eb52e6d444499` |
| `lean/MicroCFTA/EnumerationWaitingIndex.lean` | 10656 | `3dd9d39df6a289d3b9689280f0dbb786ea4609b8132016d1e4178d2ea9c0d8e5` | 13-20 | 387 | `e33eb259c7c5445b6ff49bc5d8cb2d6947eac28271153aa4fb6f579abdff5315` |
| `lean/MicroCFTA/EnumerationBuilderCaches.lean` | 27843 | `f4882be07a73362a667a994f9e37344b9fb4619565dcf53ca0e857ecd21ccb9d` | 13-40 | 1567 | `1e43672b4ef2bb3c79af04d43506352b9f96ecfe5ab0f6ef840719656dc10835` |
| `lean/MicroCFTA/EnumerationReferences.lean` | 39454 | `8c6f8fa2b6ffeb550da4b3b25bff7d5596910107d663c28987137231d61ba1fc` | 344-352 | 594 | `a57557be85babfbd55c7e13c435a8f2ab9b00084c99d427578c9c458f200deb3` |
| `lean/MicroCFTA/EnumerationDependencies.lean` | 29230 | `d0ab8f9bf345495711bc2e98fe22e188f2d0f00229f13ea2e3c4de895f294a21` | 392-393 | 193 | `69034ef6a96e4c919eb524d294c3be031cd6341e200e508eb0fa2063aa1a424e` |
| `lean/MicroCFTA/SourcePruningEnumerationObservation.lean` | 7357 | `5a7b858adc4febb75621b9836053f308924c22d5fd7662741da61cbdab629bf4` | 20-26 | 389 | `2b1c8484919f9f2169e064b5acbf5b24b4796c2ea918762b3635194e6871bfad` |
| `lean/MicroCFTA/SourceUnionFindCompression.lean` | 7887 | `1a6d2adbf6c2886ffff91935f59b7cf9d68b32fc90593e3461af823af56b38e0` | 133-153 | 1376 | `ec7c16b796d6f031f0168ad5dc8a8af4aa74497eccff05dc083e567c2e259f3a` |
| `lean/MicroCFTA/EnumerationCorrectness.lean` | 76898 | `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d` | 644-649 | 363 | `71b935f49708388e5ab84a40b48342b9b120bb53f962688f3c713e8497293bdc` |
