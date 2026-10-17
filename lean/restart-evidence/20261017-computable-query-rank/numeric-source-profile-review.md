# Numeric source-profile bounds

Frozen on 2026-10-17 at 07:50 CEST. Source: `SourceRecursiveIntersectionNumericSourceProfile.lean`, SHA256 `2c7a2c5a41dd01f1530ec4fb9ba3f909224cf46146c96a6c8f215241ac396a7f`.

The module proves numeric upper bounds for the current source profile from `InternedValueMassHeap.Stored S source`. Let N be source.nodes.next and E be source.edges.next. The public `limits_bound` gives rows <= N*S, members <= N*S, and arity <= E*S. `initial_bound` gives initialBound source <= 1+(N+E)*S. `branching N E S` is max 1 (max ((N*S)^2) (max (N*S) (E*S))). `source_branching` bounds the existing sourceBranching by that expression. `branching_mono` permits an increase in all three numeric inputs.

These upper bounds need no Facts premise. Every successful node or edge filterMap read exposes the exact issued key and actual record lookup. Stored bounds that record. A mapped sum is at most its list length times S. FilterMap length is at most the corresponding range length. Literal rows, union members, and edge children fit their complete metadata-free payload mass. The proof counts occurrences. It does not assume distinct payloads or injective identities. Pending issued identities add no successful payload, but remain included in the range length bound.

The module is generic in Symbol and Guard. It has no equality, SizeOf, semantic, closedness, query completion, future trace, or desired output premise. Mu bodies and both probes remain included in the existing mass definition. Guards and metadata are unrestricted. This is an initial source-profile bound. It does not by itself prove a computable semantic rank, instruction count, later store bound, or host word-capacity discharge.

## Validation

Production strict attempt 4 passes with an empty log. Canonical target build passes 1178 jobs in numeric-source-profile-canonical-1.log. Its only warning is the existing replayed InternedFreshOrdinaryClosedCompletion inputs warning. Imported public checks cover all five declarations with complete explicit signatures and axioms. Final imported kernels pass two complete signature/axiom pairs in numeric-source-profile-kernels-4.log. Only standard axioms occur.

The first kernel builds a recursive Mu and an ordinary value inside an explicit two-member union from the empty source. It derives its own Facts and mass store. It obtains all initial numeric bounds. It then performs actual edge construction with two occurrences of the root, derives growth and issued history, recovers the exact old root by readback, and obtains numeric source bounds from the produced later store. No resulting store or readback is assumed.

The second kernel builds one ordinary constant by actual edge and node constructors. Its complete source has Stored 3 but initialBound = 5. It proves that initialBound <= 3 is false and derives the correct counter-scaled upper bound. Thus a uniform per-payload bound cannot replace the recomputed sum without counting payload occurrences.

Production attempts 1 through 3 retain their missing-nodeEdges-namespace errors. Kernel attempts 1 through 3 retain failed simplification and unavailable-tactic diagnostics. Each attempted source and raw log is preserved. No failed log is used as final validation. No older production source, Haskell file, Audit file, or restart document changed. No Haskell behavior defect was found.
