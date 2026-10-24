# Stored pending slots to one checked query and target write

Reviewed at 2026-10-24T18:06:42+02:00. Source-only verdict: the selected narrow composition is feasible with existing APIs. It is a checked intersection and one target-slot replacement. It is not the full native assimilation operation. No new action, state, helper, scope predicate or recursive correctness proof is needed for this connection. No declaration or body is authorized by this report.

I read the complete small observation, identity, node-codec and write modules, the current TargetQuery and TargetWorkerNative APIs, and the exact native merge/write branches. I ran only source/data/hash inspections and wrote this report. I did not execute a compiler, parser, candidate, import, Git command, network operation or repository mutation.

## Exact operand and result route

1. Each input must be an actual raw list-slot equation in the SAME enumeration state, of the form stored unenumerated `(some handle)` with its actual suspended list. Apply `SourcePruningEnumerationObservation.PendingRealized`19–25 separately to those equations. This derives the complete native value, exact `lookupNode` readback, availability and `free = []` for each operand. No desired operand value, old-value equality or closure law is supplied independently. A stored `(some handle)` can decode to Empty at handle zero; it does not imply a nonempty ordinary node.

2. Tie that realized native heap literally to `before.native.machine.heap` of the checked request. Current readiness supplies coherence. If an input-handle identity is needed, `SourcePruningEnumerationIdentity.lookup_encode`11–45 derives `encodeNode actualValue = some SAME handle` from the actual lookup. This is an available route, not a required extra premise or output for the selected theorem. It uses the winner-key check and coherent stored entry, rather than choosing a replacement handle. `lookupNode` rejects missing or losing positive entries. Zero is the explicit model Empty convention. The model does not extract native NodeIds.

3. Invoke `SourceCurrentAllocatedTargetQuery.finite` once with those actual operands. Keep its full actual `Receipt`, next inventory, result and checked state. Its existing domain remains explicit: current class-scan Ready, actual inventory admission, available/closed operands, reached WordRanges for the exact empty-domain request, and the current global memo bundle with validity. Neither a supplied successful action nor result closure is an input. The receipt derives actual checked execution, final Ready, effects, machine Extension, result availability and closedness, exact language, admitted next inventory and global memo/event facts. The actual returned heap is the one used by the write. Do not rerun the query to obtain a different result or endpoint.

4. `receipt.effects.keeps` is exactly heap Keeps from the original checked heap to the returned checked heap. Apply `Observation.realized_preserved`45–54 with `EnumerationCompressionFrame.Frame.refl` on the unchanged enumeration state. This transports ALL old pending-slot realization to the returned native heap. Its proof uses both immutable record growth and issued-name history; heap coherence alone is not this transport.

5. Apply `SourcePruningEnumerationWrites.write_available_realized`42–67 at that returned heap, to the actual query result, target raw slot and suspended list `sourceScs ++ targetScs`. The target's original stored-slot equation derives the required in-range list bound. This theorem derives the result encoding, actual `Success (setValue target ...)`, exact record-update final enumeration state, exact target stored slot and realization of ALL pending slots. For the explicit SAME-result readback, `Nodes.available_readback`35–48 derives both encoding and lookup from final coherence plus the receipt's availability/closedness. Its encoded handle agrees with the write theorem's handle by the common `encodeNode result` equation; no handle-equality premise is needed. No representative lookup or union-find compression is performed by this raw write. The full query receipt is retained alongside the actual write facts.

The final enumeration state is exactly the original state with one list slot replaced. Counter, representatives, obligations and both ancestry fields are unchanged by this primitive. A raw `Frame` is not claimed across that write, because values change. PendingRealized is preserved by the existing write theorem instead. Query-state effects and enumeration-state effects remain distinct existing records; no product-state machine or native Graph is introduced.

## Existing reverse adapter: correction to earlier bounded search

The earlier ready-hit report suggested a possible decoration of exact Steps with observed Inputs to obtain physical Trace. Preserve that report as immutable search history. The third preflight identifies the already-installed `SourceCurrentAllocatedTargetWorkerNative.of_done`, `of_done_ready` and `step_iff_done`. I read that complete module. Prefer those APIs; do not author the redundant trace adapter.

`of_done`26–48 takes the literal current Demand done equation, Good, idle tables, actual closed available operands and reached WordRanges. It independently constructs a physical trace and uses completed-execution uniqueness to identify BOTH the same result and full returned checked state. It needs no supplied successful right-hand run, inventory, global memo law or NodeProduced. `of_done_ready`51–63 specializes current Ready. This route is useful if the caller already retains a done equation. The selected finite producer can use its existing receipt directly.

Closure is already derived by the CURRENT checked scope/cache producers. It does not follow from weak NodeProduced or from language equivalence alone. This stage reuses the genuine current packet; it adds no desired-closure premise and makes no claim about arbitrary unscoped warm tables.

## Native source claim and exclusions

`Enumeration.hs204–210` combines the two pending-node payloads and concatenates suspended constraints in argument order. `assimilateUvarVal502` calls it as SOURCE then TARGET. Thus `sourceScs ++ targetScs` is the correct order. The same native function reads both raw addresses from the slot map. The proposed actual list-slot premises match that raw-address boundary, not representative-resolved reads.

This component must be described as the intersection-and-target-write connection. It does not claim a completed or executed native assimilation prefix. Native assimilation492–509 also has: equal-address no-op, eliminated-source skip, optional conservative-empty normalization, unconditional empty-content rejection BEFORE writes, a target write with empty waiting deltas, source elimination, and ancestry transfer. None is proved by this selected stage. Equal target/source slots can still satisfy a raw replacement theorem, but they do not justify the native no-op branch. An Empty checked result can be encoded as zero and written by the model primitive, but native assimilation rejects empty contents before its write. There is no invented enumeration error or fabricated successful native path in either case.

The native `writeUVarValue`450–465 also updates expandable slots and canonical waiting counts. Existing enumeration `setValue`102–104 changes only `values`. This component supplies no native index correspondence, count transfer, source elimination, ancestry union, representative union, scheduling, conservative-empty policy or full assimilation result. It does not model forcing or prove the whole driver. Full Symbol/Formula and actual checked-state caches remain intact. H6 remains strongest and the whole goal remains ACTIVE.

## Input identities and prior custody

The three preflights are preserved and identity-bound below. The third report refines the first report's bounded reverse-adapter search. This report makes that correction explicit without changing prior bytes.

- `/tmp/mcfta-pruning-enumeration-ready-hit-20261024-source-review.md`: 11306 bytes; SHA-256 `03e801d54b2b87ae42257ce2083d6dc176118ff8a847ab159bc59875282ade9c`.
- `/tmp/mcfta-checked-result-20261024-preflight.md`: 25256 bytes; SHA-256 `321f4b4134e7a735e19558366fd960a25288d1b365263e6a855d1b486e8f20bb`.
- `/tmp/mcfta-checked-demand-return-inventory-20261024-review.md`: 14202 bytes; SHA-256 `3d92a91021b5c1bc4c0cf0e7b4d7efaed453750e0a45c230c3d4b816c57dcaca`.

The current `prior-custody-index.json` contains 39 records. I checked all 39 source files against the exact 39 files under `previous-publication/`, including byte lengths and SHA-256. There are no extra copy files. The index is 11,369 bytes, SHA-256 `0c4bf86bc474b55796aa6f3fe4ce2874bef6227d0e8ff8b1d07ba6f9929d175a`. This retains prior failure, correction, publication and next-assessment history. It does not assert a new seal or push.

Defining file identities follow. Parentheses give the relevant source lines. Hashes cover whole files. Paths resolve under `/home/tritlo/Code/mcfta`.

| Source and relevant cuts | Bytes | SHA-256 |
|---|---:|---|
| `lean/MicroCFTA/SourcePruningEnumerationObservation.lean` (19–25,45–54) | 7357 | `5a7b858adc4febb75621b9836053f308924c22d5fd7662741da61cbdab629bf4` |
| `lean/MicroCFTA/SourcePruningEnumerationIdentity.lean` (11–45) | 2939 | `e260eceaa5ed848c94155530c24ccca7c99092db0091b8b9e6174c33894e7361` |
| `lean/MicroCFTA/SourcePruningEnumerationNodes.lean` (16–32,35–48,51–74) | 3546 | `1fb4077739402c31ec48d4bfa8254ef9c1b7453601290dfcd1c0c0031eeee8a4` |
| `lean/MicroCFTA/SourcePruningEnumerationWrites.lean` (42–67) | 4216 | `32864f9158615ee7787c7490356471489978a5622ea984d904f7b03329510a7e` |
| `lean/MicroCFTA/SourceCurrentAllocatedTargetQuery.lean` (31–69,73–117) | 8024 | `20231be214e9d62e97f92b41d32fce62be959e78e24141c9a7fe73dd2060e9a6` |
| `lean/MicroCFTA/SourceCurrentAllocatedTargetWorkerNative.lean` (26–79) | 4880 | `1bcd61ce26ff5f8f33f636b3ec18e1cf8d063babbc3cd76d52cba863619dd619` |
| `lean/MicroCFTA/SourceCurrentConjunctionRowsAllocation.lean` (40–44) | 12076 | `08dcbbbf50ececa84dc2d7328100ddc50074c88ee76bd5c7e121c08d1527ca88` |
| `lean/MicroCFTA/EnumerationState.lean` (102–104) | 33489 | `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4` |
| `cfta/src/Data/CFTA/Enumeration.hs` (199–222,429–465,490–509) | 71269 | `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` |
