# CPS proof repairs

Created 2026-11-14 at 06:51 CET. Status: UNCOMPILED. Root must compile this source.

The candidate changes four proof bodies. It preserves all eight theorem headers and every byte outside the proof bodies. It adds no definition, hypothesis, provider, gate, or runtime hook. The imported five maps and the actual native workers remain unchanged.

Use `candidate/SourcePruningEnumerationIdentityChildMetadataErasure.lean` for the proof-only patch. Use `instrumented/SourcePruningEnumerationIdentityChildMetadataErasure.lean` for a private check with eight corrected axiom prints. The two copies have identical declarations and proofs. The only difference is the namespace in the eight print commands.

## Diagnostic repairs

- In `consumeSelected_erasure`, reduce the selected receipt match before splitting the actual continuation or advance result. This exposes the same expressions on both sides. It addresses errors at original lines 134, 141, and 142.
- In `visitCapturedWith_transport`, reduce the complete receipt match before splitting the finalization result. This addresses errors at original lines 166 and 168.
- In `eagerChild_erasure`, supply the complete well-founded induction motive after generalizing the continuation arguments. It has exactly the original theorem conclusion. This addresses original line 189. The two local child proofs use `simpa` without redundant reduction rules. The negative ordinary branch also reduces `false = true` before applying shallow transport. These branches were hidden by the motive error.
- In `runWithChild_transport`, add `Bool.false_eq_true` before reducing the negative terminal branch. This exposes the actual scan. It addresses the missing rewrite at original line 292 and the unused reduction rule at line 285.

## Instrumentation repair

All eight original print commands name `IdentityChildMetadataErasure`. The declarations are in `IdentityResultMetadataErasure`. The proof-only candidate retains the original commands. The separate instrumentation patch corrects these eight names. It does not rename declarations.

## Checks performed without a compiler

The input SHA equals the exact source reported by Root. All eight theorem headers match byte for byte. A proof eraser confirms that all bytes outside proof bodies match in the proof-only candidate. GNU patch applies both patches with zero fuzz and reverses them to the exact input bytes. `checks.json` pins the original source, the immutable diagnostic log, the five-map input, and the actual worker helpers. No compiler, live source, Git, Haskell, or board operation ran.

The earlier v1, v2, Root check2, and map check3 inputs remain untouched. These checks provide source integrity only. They do not provide Lean proof credit.
