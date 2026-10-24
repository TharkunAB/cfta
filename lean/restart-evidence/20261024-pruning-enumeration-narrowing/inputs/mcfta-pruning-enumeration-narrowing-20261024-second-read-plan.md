# Coupling computed narrowing with the actual second representative read

Source-only assessment at 2026-10-24 06:11 CEST. The direction is suitable for at most two small modules. No declaration or body is authored here. The earlier consumer review and all owners remain unchanged.

The smallest useful next result starts with an actual pending `getValue` success. It derives the old native-model value, runs the existing modeled narrowing computation, and, only in the changed surviving branch, constructs an actual finite representative read followed by the existing `setValue`. It retains the first read, every compression frame, the actual native-model heap and all final realized slots. It does not accept an equality between an arbitrary oracle/narrow function and the desired result.

## State order and necessary inputs

Keep five enumeration states distinct:

- B: before the actual pending value read.
- R: after that `getValue` read.
- E: entry to the source `expand n scs` action. In the ordinary path E is R. A nonrepeated recursive-boundary check can first compress the forest.
- Q: after the second representative read, executed only for a changed surviving result.
- F: after the raw-slot write in that changed branch.

Keep the native-model heap H and its actual returned heap H' separate from these states. Narrowing changes H to H'; it does not change the enumeration state E.

The useful input packet is Ready H, PendingRealized H B, Total B.representatives, the actual pending `getValue` success B to R with its old handle and ordered `scs`, and the existing `fits`, `admits`, key and EdgeKey equality instance. The selected original raw uv remains fixed. No old encoding, decoded output value, desired root, successful second read, new result, new cache certificate or StorageValid premise is needed.

For a theorem that crosses `checkRepeated`, retain its actual false-result success R to E and derive its frame. This is an observed branch condition of the existing prefix, not an assumed callback equality or proof of eventual enumeration success. A first theorem may instead start at the actual expand-entry state with a retained first-read/frame packet. It must state that smaller boundary clearly.

## Stage 1: actual repeated read and slot correlation

Propose one small observation module, with no new state predicate or action definition. Its main result packages the following existing facts for an actual pending read. A small false-branch frame lemma can share this module if the Until adapter is included.

1. Invert the actual first `getValue` with `getValue_success`. It derives a concrete `found`, the successful findRoot equation, the actual slot read at `found.representative`, and R's exact forest update. `getValue_frame` gives Frame B R and finite root paths in both forests. The slot bound follows from the successful list lookup, without a global allocation bound.
2. If actual `checkRepeated` returned false, derive Frame R E. On a nonrecursive view this action is pure. On a recursive view, invert its actual representative read and use `representative_frame`. The true/write branch contradicts the observed false result. No CompleteGraph, Safe or Ready-uv premise is required for this frame fact.
3. Transport the first root path through the frame to E. `UnionFind.findRoot_terminates` constructs a finite successful findRoot there. Its correctness and `reaches_unique` identify its returned root with the first read's root. `representative_success` reconstructs the actual second representative action E to Q.
4. `representative_frame`, with Total transported from B, gives Frame E Q. Its values equality retains the SAME pending slot, old handle and ordered `scs` in Q. The earlier successful lookup gives the write bound in Q. Retain Q's actual forest from the successful lookup; do not identify Q with E.

There is an equivalent route through existing `representative_transport`: recover the first representative success from the first getValue inversion, then transport it from B to E across the derived frame. This already gives the same actual root and a finite second read. No new primitive termination theorem is missing. Use whichever route yields the smaller proof.

The missing public packaging is a finite reread-and-slot result, not another success-conditional equality theorem. `getValue_repeat_value` already covers consecutive successful value reads, but neither produces the second execution nor retains its raw write destination. A second full getValue action would also add a source read that the changed branch does not perform.

No existing generic false-result `checkRepeated` full-frame lemma was found in the bounded API inspection. Existing `checkRepeated_ready` requires the stronger selected-root Ready packet. Existing `checkRepeated_terminates` requires CompleteGraph and excludes recursive views. Neither is the right replacement for the actual false-branch frame derivation above.

## Stage 2: one computed narrowing and the literal changed branch

Propose one consumer module importing Stage 1, the completed codec inverse and all-fuel Empty equation, NativeView, observation and Writes. Prefer one main result with a branch packet over a new combined monad, graph, callback or generic validation layer.

Derive the old complete value from realization at the actual first root slot in B. Derive its exact old-handle encoding with the new inverse. Use `narrowAt_complete` once on this value and H. Retain its rows, intermediate heap, actual constructor equation, returned result and H', Keeps, result availability/closedness, Ordinary and Empty laws. Derive the result's encoded handle and complete lookup in H'.

The all-fuel Empty equation excludes an old Empty value whenever the computed result survives. Closedness excludes references. Thus the surviving model identity comparison is defined on both values; nonemptiness is derived, not an extra input.

Retain the native-model outcome in every branch, then follow the source branch order:

- Empty: reject before identity, rereading or writing. State that the rejected action has no successful output. Do not claim Q or F was executed. The native-model computation still has its actual H' and Keeps evidence.
- Equal surviving handles: retained old lookup plus new lookup in H' gives equality of the SAME complete values. The continuation is pure at E, so F is exactly E. It is not necessarily B: the first read or boundary check may already have compressed the forest. Preserve realization by composing Frame B E with the actual Keeps H H'. Do not infer H' equals H.
- Different surviving handles: invoke Stage 1's finite second read only here. It derives the actual root and Q. Transport every pending realization from B to Q using the composed frame and actual Keeps H H'. Apply `write_available_realized` to Q, the returned value, that root and the SAME `scs`. Its derived written encoding identifies its handle with the computed new handle. Retain actual success of the bind of representative and setValue, the exact record update from Q to F, final slot read and PendingRealized H' F.

The changed result must explicitly contain both Frame E Q and F = Q with only its value array replaced at the returned root. Do not claim Frame E F or Frame B F: a changed write changes `values`, which is a field of Frame. Counter, obligations and both ancestry fields are unchanged by the write; the forest is Q's actual compressed forest. Full realization is the post-write invariant.

This is a computed narrowing suffix, not the pure Nat-parametric `EnumerationUntil` theorem. Its inputs contain no desired narrowing result or equality with the arbitrary `narrow` argument accepted by Until. Root can later compose a source-specific caller after proving that independent correspondence. There is no need to invent it as a premise now.

## One common bound without another execution

NativeView supplies retention of the SAME result and H' at every larger narrowing bound. `getValue_moreFuel` and `representative_moreFuel` retain their exact intermediate enumeration states. `checkRepeated_moreFuel` does the same if that prefix is included. Choose a finite sum of the witnessed bounds, then extend each existing success to that common bound. A positive common bound can be expressed as the driver predecessor plus one. No new read, native computation or unrelated second run supplies the retained endpoints.

A Frame alone does not assert equal fuel suffices in different forests. Derive the second sufficient bound first. Do not reuse the original bound merely because both reads return the same root. The finite common-bound corollary is enough to fit the driver's same-bound calls later.

## Minimum scope and remaining boundaries

There are no missing primitive read inversion or termination APIs. The new work is the bounded packet assembly, plus the false-result checkRepeated frame fact if crossing that prefix. A reasonable pre-declaration estimate is 60–100 ordinary lines for Stage 1 and 110–170 for Stage 2, including explicit local types and layout. These are estimates, not caps or proof claims. Exact declarations and inventories must determine final budgets. Do not add paired-observer, generic result uniqueness or whole-loop theorems for this step.

Preserve the original selected raw uv for Pruning.narrow's type-position membership and `holeKey`. The second read returns the write destination; it does not replace that input ID. Mu and incoming type-position bypasses belong to the later caller composition. Union is not exempt. The actual false recursive-boundary branch must retain its forest effects; the true branch skips expansion and is outside this narrowing suffix.

Model handle identity and complete retained lookup do not establish native NodeId/Int extraction, native setUVarValue's waiting/expandable cache maintenance, or graph.node classification from the encoded handle. Native memo2, lazy forcing, fits/admits/typing correspondence and general intersection remain separate. No oracle acceptance, resource, convergence, Haskell repair or stronger H6 claim follows. Arbitrary `scs` is retained; StorageValid is not silently obtained from that fact.

## Source cuts and actual read scope

I read the complete small observations and node-observer modules and the exact bounded API cuts listed here. I reused prior complete reviews of the unchanged NativeView, codec, realized-observation and Writes modules by live hash. I did not manually read every line of the large Correctness, Driver, Schedule or Execution files.

- Native Enumeration.hs978–1005: Empty/identity/second-representative/write order and intervening recursive-boundary branch.
- Native Pruning.hs127–141: bypasses, original raw key and actual narrowAt helper.
- EnumerationUntil.lean95–124: first getValue, checkRepeated and changed representative/setValue sequence.
- EnumerationCorrectness.lean37–60,1010–1035: Success, bind/pure inversion and actual getValue inversion.
- EnumerationSchedule.lean54–65: actual representative inversion.
- EnumerationCompressionFrame.lean20–51,69–88: complete frame, totality and actual read frames.
- EnumerationObservations.lean32–104: paired reads and constructive representative/getValue transport.
- EnumerationExecution.lean99–111,244–250,413–420: larger-bound retention and representative termination.
- EnumerationUntilBridge.lean78–99: existing consecutive getValue agreement.
- EnumerationDriver.lean431–474: actual recursive-boundary action and stronger existing Ready lemma.
- EnumerationTermination.lean41–47: existing CompleteGraph-only nonrepeated result.
- UnionFind.lean43–61,124–176: root paths, uniqueness, successful read correctness and termination.
- SourcePruningNativeView.lean60–79; SourcePruningEnumerationObservation.lean19–80; SourcePruningEnumerationWrites.lean41–67; SourcePruningEnumerationNodes.lean16–74: actual coupled model foundations.

The final source-identity table below is part of this review cut. Root's new inverse/Empty prerequisites are pending separate review and are not claimed installed here.

Repository root: `/home/tritlo/Code/mcfta`. Source paths below are relative to that root.

| Source | Bytes | SHA-256 |
| --- | ---: | --- |
| `lean/MicroCFTA/EnumerationCorrectness.lean` | 76898 | `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d` |
| `lean/MicroCFTA/EnumerationSchedule.lean` | 86287 | `3e84f2059725b3c0392d4df005574fde2918290cb393c4be0d549a62ad4a4e45` |
| `lean/MicroCFTA/EnumerationCompressionFrame.lean` | 8220 | `5b6e6a4b11c21b949874db500e23aa074fcdd4e0de683f46f33863113dc91375` |
| `lean/MicroCFTA/EnumerationObservations.lean` | 6136 | `ebc891e8461c7b545d55f6823322789f19635e2d1c58a5551307b621079ba0ab` |
| `lean/MicroCFTA/EnumerationExecution.lean` | 30176 | `b81e03600e03085ec32fc8c85026ca4af562593764b28d6f8dd776eb3ac98346` |
| `lean/MicroCFTA/EnumerationUntil.lean` | 8864 | `3d54b3a6ca3db0c668f6b8910c62adcae099f3eae79cfb6d82ee9176710fd137` |
| `lean/MicroCFTA/EnumerationUntilBridge.lean` | 14619 | `ac5eb73483f5d59bf52f1a251c55322050f289cc8a9dd052d032ab8e32638642` |
| `lean/MicroCFTA/EnumerationDriver.lean` | 52410 | `0769d78e4d3c01d959cf21c5a59642fee164dc60655e86601458a799da72bbcf` |
| `lean/MicroCFTA/EnumerationTermination.lean` | 13991 | `8ff05dc551296ff882eec1ab1b41c96eeed3096555f00eb7bde678b0ebb113cc` |
| `lean/MicroCFTA/EnumerationNodeObservation.lean` | 4323 | `0dc7f259885a4c5a914aed2d7a62030b18cc87fc37962ffe438c146b6459d06d` |
| `lean/MicroCFTA/UnionFind.lean` | 41077 | `3668867a41890e4721c301092a06c48d3bd757a8eede4b92340fe5db80119a14` |
| `lean/MicroCFTA/SourcePruningNativeView.lean` | 10881 | `0cf2d0d30d1a231dd6a1c53dc8a78bc0b8c37972ff5fe3d55b2767e9f6f98571` |
| `lean/MicroCFTA/SourcePruningEnumerationNodes.lean` | 3546 | `1fb4077739402c31ec48d4bfa8254ef9c1b7453601290dfcd1c0c0031eeee8a4` |
| `lean/MicroCFTA/SourcePruningEnumerationObservation.lean` | 7357 | `5a7b858adc4febb75621b9836053f308924c22d5fd7662741da61cbdab629bf4` |
| `lean/MicroCFTA/SourcePruningEnumerationWrites.lean` | 4216 | `32864f9158615ee7787c7490356471489978a5622ea984d904f7b03329510a7e` |
| `cfta/src/Data/CFTA/Enumeration.hs` | 71269 | `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` |
| `specftacular/src/Specftacular/Pruning.hs` | 16989 | `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61` |

Unchanged earlier assessment: `/tmp/mcfta-pruning-enumeration-narrowing-20261024-consumer-review.md`, 10134 bytes, SHA-256 `f5ee0cfd8f15c9b0d10cada7e8f90213a13f56d42710624f5b55aa85478ec5e2`.

Arity authored the earlier narrowing plan. Root authored the installed narrowing, observation and Writes bodies. I did not author those bodies. This review changes only its own /tmp report. No compiler, prepared program, Git, network, board or repository action was performed.
