# Root profiles for repaired ordinary probe selection

`InternedFreshOrdinaryProfiles.build_profile` proves the complete repaired
executor's abstract root profile from the original syntax and input
profiles. The mutual theorem also covers child lists and edge lists.
`closed_heap` derives the recursive profile invariant from empty caches.
`closed_profile` relates every completed closed result to the existing pure
syntax interpreter. Both raw and smart binders use the repaired executor.

`InternedFreshOrdinaryProfileHeap.Correct` decodes the two stored probe
profiles at `Depth` and `U (ordinaryLevel depth)`. The old invariant at
`U depth.depth` is not an assumption. The new heap starts empty and is
preserved by actual constructor effects. A canonical cache hit recovers
the exact stored probes from complete resident record equality.

`InternedFreshOrdinaryProfileCandidate` reuses the existing primitive
`smart_evaluate` proof. Its decoder accepts any natural ordinary level, so
it also accepts the repaired level. The candidate proof uses the actual
Depth, ordinary, and fresh-body profile results. It assumes no whole-body
callback equality law.

`InternedFreshOrdinaryProfileExecutionFacts` composes the repaired body's
result with the actual self-reference filter. The request module uses
repaired normalization, record facts, and pending-slot preservation. A
miss derives the new stored candidate invariant. A hit uses the new heap.
A pending return preserves every completed record and claims no result.
The full structural induction discharges the recursive profile premises.

The existing generic complete-probe readback, fresh interned-name fact,
primitive cleanup interpretation, and pure decoder proofs are reused.
These facts do not require the old depth-specific heap. Old modules and
counterexamples remain unchanged.

Profiles describe the abstract root alternatives and free reference names.
They do not give the full accepted-term language. The new theorems do not
prove general no-pending, completion, or global binder callback equality.
They establish the semantic layer needed by the repaired free-name proofs.

All five modules pass the pinned Lean 4.34.1 build. Explicit signature
checks confirm that the theorems use `InternedFreshOrdinaryConstruction.build`.
The isolated audit checked 8,522 imported theorem dependencies with only
`propext`, `Classical.choice`, and `Quot.sound`. Its temporary driver is
/tmp/mcfta-fresh-profile-audit.lean.
