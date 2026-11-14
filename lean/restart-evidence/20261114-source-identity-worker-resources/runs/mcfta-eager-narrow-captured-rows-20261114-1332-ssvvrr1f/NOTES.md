# Captured rows with actual narrowing

Created: 2026-11-14 13:32 CET.

The candidate changes only ActualCapturedRowsResources in lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean.
It adds private eager_captured_rows_resources_with_narrow.
The helper takes the actual narrow operation and EagerResumeWithNarrowComplete.
Its existing row induction calls the checked eager_captured_resources_with_narrow.
The induction body has no other changes.
The old eager_captured_rows_resources header is byte-for-byte unchanged.
Its new proof specializes the generic helper at SourcePruningOuterNarrow.narrow.
No operational definition or child, tuple, or row kernel changes.
No Key, fits, admits, or future-provider hypothesis is added to the generic helper.

Source SHA-256: 1f537303110606e498d6a9cd1f7e1f87287f9485b0af87bd1bcc648f9f57e11a
Candidate SHA-256: 4626e813b71adfee4b13cc62381593a5b5ce2959ff90beba1c97c39a5ae1cb69
Line delta: +63.

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

Files:
- SourcePruningEnumerationSharedEagerReservation.lean: full candidate.
- original.lean: exact input.
- captured-rows.patch: minimal unified diff.
- original-section.lean and candidate-section.lean: section comparison.
- configured-header.lean: exact old configured header.
- checks.json: static preservation checks.
- SHA256SUMS: packet hashes, excluding itself.
