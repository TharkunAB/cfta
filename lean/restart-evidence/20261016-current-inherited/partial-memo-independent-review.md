# Independent review of the current caller result cells

Reviewed at 2026-10-16 10:26 CEST. No material defect found.

The review used these frozen source files:

- `SourceCurrentAllocatedPartialState.lean`, 250 lines, SHA256 `631ba3b6bde5f91c45b3b82fe9332f1c1a43f62a46723b56dda64f4f547b09da`.
- `SourceCurrentAllocatedPartialMemoSound.lean`, 384 lines, SHA256 `d9954897cde59e88abb27f68fde9842f60662f862847ede783193283fe3c8d7e`.

## Stored owner and later candidate

`beginNode` and `beginEdge` execute `FlatMemoThunk.lookupOrInsert` before `demand`. A warm suspended cell starts its stored original request. It does not replace that request with the later candidate. A returned hit returns its stored result and the identical complete caller state. A busy hit remains busy. The two result families have separate keys and tables.

The new evaluate wrappers derive the exact retained owner and its evaluating cell from the actual begin equation. They derive equality of owner and candidate keys. They do not assume equality of the complete requests. This distinction is required for inherited constraints whose physical identity has several equivalent representations.

The ready wrappers obtain the old owner law from the returned cell. `NodeLaw.of_key` and `EdgeLaw.of_key` then transport that law to the candidate. This transfer requires a common valid equality interner, a common coherent constructor heap, both inherited values' readiness, and both inputs' residency. Equal node references determine the complete resident node. Equal edge identities determine the complete resident edge. Equal inherited identities determine satisfaction equivalence through the existing key transport theorem. No candidate result law or desired output equality is supplied.

## Publication, completion, and advancement

`Sound` retains inherited readiness and input residency in every phase. It requires result residency and the independent language law only for returned cells. New publication therefore needs the current input facts, not a future result law. `initial_sound` is vacuous for the two empty result families. It does not establish checked-machine readiness or coherence.

The fresh-miss equations identify the newly published request and its exact evaluating cell. Raw equations apply even to malformed states. Preservation theorems additionally use structural validity, whose bounded handles exclude an overwrite at `next` and whose key links exclude dangling published handles.

`finishNode_sound` and `finishEdge_sound` require an exact current evaluating owner cell, a resident actual result, and the independently proved local law for that owner. They preserve the owner and install the returned result through the actual finish operation. This is the correct local finish obligation. It is not a body completion theorem. A later finish cannot replace a returned winner.

`Sound.advance` uses actual physical effects to transport inherited readiness and input/result residency. The result laws quantify over immutable values and all ambient languages. They do not depend on a mutable finite input model. The operation-table extension transports stored inherited identities. Both result tables remain literal copies under advancement. The theorem does not claim readiness or correctness for arbitrary replacement merge and fourth tables.

## Remaining obligations

The caller proof must derive each owner body law before finish. It must also retain the exact running frame across the body. A running equation at publication alone does not establish that equation at the later finish. These modules do not prove general recursive caller termination, successful handling of busy observations, or global memo receipts for a completed body.

The source connection remains a serial logical demand protocol. It does not prove GHC thunk forcing order, blackhole behavior, concurrent publication, native container equivalence, or machine identity bounds. Separate checked readiness, coherent heap, valid equality interner, merge/fourth correctness, and global memo invariants remain explicit where required.

## Validation inspected

The source review followed the actual `FlatMemoThunk` lookup, demand, finish, running, and returned laws. It also checked the existing partial-key transport and resident edge identity lemmas. No proof source was changed, and no duplicate build was run.

The owner's focused build log `partial-memo-sound-build-1.log` records a successful 1119-job canonical build. Its old dependency warning is unchanged. This review records that existing build evidence; it is not an independent build result.
