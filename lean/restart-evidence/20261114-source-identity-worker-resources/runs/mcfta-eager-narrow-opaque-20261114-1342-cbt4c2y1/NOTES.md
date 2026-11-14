# Opaque resources with actual narrowing

Created: 2026-11-14 13:42 CET.

The candidate changes only ActualOpaqueResources in lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean.
It adds private eager_opaque_resources_with_narrow.
The helper takes the actual narrow operation and EagerResumeWithNarrowComplete.
Its existing proof calls the checked callback_eager_induction_resources_with_narrow.
The proof body has no other changes.
The opaque branch has no direct dependency on captured rows.
The already checked generic captured-row helper remains unchanged.
The old eager_opaque_resources header is byte-for-byte unchanged.
Its new proof specializes the generic helper at SourcePruningOuterNarrow.narrow.
No operational definition or child, tuple, or row kernel changes.
ActualPreparedResources and the whole-worker stages remain unchanged.
No Key, fits, admits, or future-provider hypothesis is added to the generic helper.

Source SHA-256: 4626e813b71adfee4b13cc62381593a5b5ce2959ff90beba1c97c39a5ae1cb69
Candidate SHA-256: 7ed746108fd83a2884ea0612f9feb7448195577cc91b00b364b101254115ec60
Line delta: +47.

Static checks confirm exact bytes outside this section and the configured header.
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
The final identity-worker theorem must not gain artificial Key, fits, admits,
or future-provider premises.

Files:
- SourcePruningEnumerationSharedEagerReservation.lean: full candidate.
- original.lean: exact input.
- opaque.patch: minimal unified diff.
- original-section.lean and candidate-section.lean: section comparison.
- configured-header.lean: exact old configured header.
- checks.json: static preservation checks.
- SHA256SUMS: packet hashes, excluding itself.
