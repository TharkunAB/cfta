# Narrowing consumer assessment

Review cut: 2026-10-24 06:01 CEST. SOURCE-ONLY DIRECTION CLEAR, with the prerequisites and composition boundaries below. This is not an exact declaration acceptance or a new proof result.

Arity authored the frozen plan. Root authored the installed narrowing, observation and Writes bodies. I did not author that plan or those bodies. I reviewed the source and retained prior source-review identities. I ran no compiler, prepared program, Git command or test. I changed no repository or owner file.

## Minimum next proof

The proposed order is suitable: first prove the actual codec inverse, then compose one computed narrowing with one realized raw slot. Do not add a complete-value uniqueness theorem or a new state predicate for this step.

1. `lookup_encode` needs genuine `Coherent heap` and the actual successful `lookupNode heap oldHandle = some oldValue`. Coherence is necessary. An arbitrary payload table can associate a positive handle with Empty or with an unrelated entry. In the positive case, the decoder's issued key, canonical table entry and winning identity test identify the entry obtained from `Coherent.nodes`. `NodeFields` and `fields_entry` then determine the encoding. No Ready, Available, closedness, Constructed or equality instance is needed for this inverse itself. The installed 76-line codec does not yet export it at this cut.
2. Record the direct equation for narrowing Empty: for every fuel, the existing `narrowAt` returns Empty with the same heap. `nodeEdges` reads Empty as an empty list; filtering leaves that list empty; `makeNode` and `run` perform no request. This is an equation of the existing operations. It needs no readiness or supplied nonemptiness assumption. It is distinct from the existing Mu bypass equation for `emptyAt`.

These are the minimum missing prerequisites for the proposed model-level raw-slot component. They do not discharge the later Haskell representation or whole-driver obligations.

## The coupled result must retain the same witnesses

Incoming `PendingRealized heap before` plus the actual slot read derives the complete old value, its successful lookup, Available and closedness. Use the new inverse to encode that exact old value at the captured old handle. A second existential forward readback alone does not identify its handle with the slot's handle.

Use `narrowAt_complete` once on that value and heap. Retain its read rows, intermediate heap, actual construction equation, returned result, final heap, Keeps, availability, closedness, Ordinary result and Empty law. These are outputs of the existing Lean computation. They are not a proof of Haskell heap extraction or native execution correspondence.

Derive the result handle in that final heap with `available_readback`. Obtain its coherence from Keeps.ready. Transport every old realized slot along the same Keeps with `realized_preserved` and `Frame.refl before`. This transport must precede the final write; retaining only the current slot loses the invariant for other pending slots.

Test Empty before identity or writing. The source rejects Empty before calling the partial `nodeIdentity`. The rejected branch may retain the actual computed native-model result and heap as evidence. It must not claim a successful final enumeration action. A nonempty-result input would omit this required branch.

For equal model handles, retain the old lookup in the final heap with `lookupNode_keeps`. Compare it with the new lookup at that same handle. Functionality of this one lookup yields equality of the complete values, including all payload fields. No reference-only identity law is needed. The successful enumeration action is pure and leaves its full enumeration state unchanged. The native-model final heap remains the actual returned heap; equal values do not imply that construction had no cache effects.

For unequal handles, the original successful slot read supplies the list bound. Apply `write_available_realized` in the final native-model heap to the returned value, transported realization and unchanged ordered `scs`. Its encoding identifies the existential written handle with the computed new handle. Retain actual `setValue` success, the exact full-record update, the new slot read and realization for all slots. Arbitrary `scs` is valid for this invariant. It does not supply StorageValid, Safe or a waiting-count invariant.

## Exact source boundaries

- Native `Enumeration.hs981–1005` first reads the representative's value. Its changed branch performs another `getUVarRepresentative uv` immediately before `setUVarValue`. `EnumerationUntil.lean106–124` retains the same second-read structure. A theorem about a supplied realized raw slot is a useful component, but is not this whole action. Later composition must retain the actual second read, its returned slot and full compression frame. The earlier `observed_realized` conclusion does not by itself expose that slot witness; the existing `getValue_success` inversion does. Do not assume an unchanged forest or write a representative chosen independently of the observed execution.
- Source `Pruning.hs127–141` bypasses narrowing for Mu and for membership of the original selected raw `uv` in the incoming type-position set. Its `holeKey` also uses that original raw `uv`. The write destination is a representative slot. These IDs have different roles. Substituting the representative into the membership or key test is not justified. Union is not a bypass. The proposed raw-slot theorem should remain conditional on an actual call of `narrowAt`; a later caller theorem must compose both bypasses explicitly.
- In a surviving actual narrowing, the direct Empty equation excludes an old Empty value. Closedness excludes references. The model identity is therefore defined on both values. Its Nat identity and the codec's successor handle can be compared by successor injectivity. Native `NodeId` is an `Int`, is not dense, and has no verified extraction relation here. The model's Empty-zero and positive-successor convention does not establish that relation or machine-counter bounds.
- `EnumerationUntil` takes a pure `OracleState -> Nat -> Nat -> Nat` narrow function and classifies its result through a supplied graph. It carries no interned constructor heap. No current theorem connects that arbitrary function or graph-node classification to the computed `narrowAt` result/handle. Keep the actual heap and computed result in the consumer packet. Do not assert a whole-loop bridge by silently equating the pure function with this computation.
- `narrowAt_complete` is structural for the supplied `fits`, `admits` and key. It does not derive their relation to native typing, `holeKey`, general intersection, memo2 or a solver. Preserve that boundary rather than describing the result as end-to-end type-pruning correctness.
- The modeled `setValue` updates only `values`. Native `setUVarValue` also maintains `_expandableUVars` and `_waitingUVars`. The same original suspended constraints are preserved, but native count/index maintenance still needs its own correspondence. Prior canonical cached-selection results do not add those fields to the Writes theorem.
- Native laziness and memo realization remain separate. In particular, `typedTypes` sequences all ordered observer reads, while pure `or` can force only a prefix of `emptyAt` thunks. This narrowing consumer neither proves that every such constructor call occurs nor changes the frozen laziness caveat. No actual failure stream, graph initialization, general assimilation or global driver soundness follows.

H6 remains the strongest combined result. No new Haskell repair, whole-pass, resource or convergence claim is justified by this assessment.

## Read scope and retained identities

I read the complete 50-line frozen plan and its companion record. All 14 complete source hashes and all 22 bounded cut hashes in that record match the live files. I read the exact native narrow/emptyAt and expand branches, the raw getter/setter and index-maintenance code, and the corresponding model operations. I reused prior complete source reviews of the unchanged 177-line NativeView, 122-line observation, 76-line codec and 69-line Writes modules, with current identity checks. This is not a new complete manual review of every dependency or native source file.

The main cuts are native Enumeration328–351,383–471,940–1010; Pruning85–143; Interned/Type64–72,359–367; model Nodes16–74, observation19–80, Writes41–67, NativeView20–79, comparison37–42, exposure37–48, constructor run122–126/makeNode248–253, coherence18–35/411–435, required cache19–43, EnumerationUntil89–124, EnumerationState103–126 and CompressionFrame20–39.

SHA-256 identities:

- Frozen plan: `65e330aa64bd4a25b172edc3daefd69530ffef22a1a6ee8147387edf272ba07a` (9466 bytes).
- Plan freeze record: `282ffb32377c790d3fa90c8f2d12e7c4a344634a1aaf36ecd3af2ee82293a648` (9370 bytes). It records all 14 source and 22 cut identities.
- Native Enumeration.hs: `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07`.
- Native Pruning.hs: `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61`.
- Native Interned/Type.hs: `f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77`.
- Nodes: `1fb4077739402c31ec48d4bfa8254ef9c1b7453601290dfcd1c0c0031eeee8a4`.
- Observation: `5a7b858adc4febb75621b9836053f308924c22d5fd7662741da61cbdab629bf4`.
- Writes: `32864f9158615ee7787c7490356471489978a5622ea984d904f7b03329510a7e`.
- NativeView: `0cf2d0d30d1a231dd6a1c53dc8a78bc0b8c37972ff5fe3d55b2767e9f6f98571`.
- EnumerationUntil: `3d54b3a6ca3db0c668f6b8910c62adcae099f3eae79cfb6d82ee9176710fd137`.
- EnumerationState: `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4`.
- EnumerationCompressionFrame: `5b6e6a4b11c21b949874db500e23aa074fcdd4e0de683f46f33863113dc91375`.
- Frozen laziness caveat: `5092036015751e05b5c8ad5ac554c8fa463bff9ff43060a1cea4b25a6611d444`.

All owner plans, prior reviews and installed sources remain unchanged. This assessment contains no theorem header or body.
