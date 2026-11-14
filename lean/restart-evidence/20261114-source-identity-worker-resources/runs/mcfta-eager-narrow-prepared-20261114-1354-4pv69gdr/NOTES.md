# Prepared resources with actual narrowing

Created: 2026-11-14 13:54 CET.

The candidate changes only ActualPreparedResources in lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean.
It adds private eager_prepared_resources_with_narrow.
The helper takes the actual narrow operation and EagerResumeWithNarrowComplete.
The callback hook uses resumeWithNarrow with that same operation.
The ordinary branch calls eager_captured_rows_resources_with_narrow.
The opaque branch calls eager_opaque_resources_with_narrow.
These are the only changes in the proof body.
The actual preparation read, heap, packet, and callback composition proofs remain.
The old eager_prepared_resources header is byte-for-byte unchanged.
Its new proof specializes the generic helper at SourcePruningOuterNarrow.narrow.
No operational definition or child, tuple, or row kernel changes.
Expansion and recursive-depth stages remain unchanged.
No Key, fits, admits, or future-provider hypothesis is added to the generic helper.
No prefix-provider hypothesis is added.

Source SHA-256: 7ed746108fd83a2884ea0612f9feb7448195577cc91b00b364b101254115ec60
Candidate SHA-256: c24787902552349475663ab7fff7924eb9d0a1808f0a753e0ec90ee39998ec58
Line delta: +45.

Static checks confirm exact bytes outside this section and the configured header.
The proof body exactly recovers the original after its four substitutions are reversed.
The live source was not changed. No Lean, Lake, Nix, heavy job, Git write,
network request, board operation, or subagent was run.
The candidate is UNCOMPILED. The root must inspect and compile it.

This helper prepares composition only. It does not prove one finite accepted
term of the same original root with one consistent assignment for every actual
emitted partial root, including parked backward recompletion. Original typing,
depth adequacy and completeness, default LPO, reduction and refolding, both
language directions, stream order, multiplicity and lazy demand, exact accepted
terms per node-count size, counts, weights, training, both rank/unrank inverses,
host bounds and compiled Haskell correspondence remain in scope and open.
The final identity-worker theorem must derive its prefix capability from the
actual identity checkpoint. It must not gain artificial Key, fits, admits,
or future-provider premises.

Files:
- SourcePruningEnumerationSharedEagerReservation.lean: full candidate.
- original.lean: exact input.
- prepared.patch: minimal unified diff.
- original-section.lean and candidate-section.lean: section comparison.
- configured-header.lean: exact old configured header.
- checks.json: static preservation checks.
- SHA256SUMS: packet hashes, excluding itself.
