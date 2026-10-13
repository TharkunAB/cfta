# Source constructor correspondence for root profiles

`InternedRootProfileNode.profile_empty_iff` proves that a pure empty profile
is exactly EmptyNode for available records with the source cardinality
invariant. `makeNode_profile_children` derives the actual ordinary-node
profile from the original edge and child empty decisions. It uses complete
canonical readback.

`InternedRootProfileUnion.makeUnion_profile` proves profile equivalence
through source flattening, first-identity removal, singleton collapse,
ordinary-node merging, and complete union readback. Equivalence preserves
opacity and the set of literal references. It does not assert list equality.

`InternedRootProfileReflection.pure_free` identifies the exact free-name
set of a pure available record. `profile_single_iff` identifies a bare
reference from a singleton profile under the independently derived source
normalization invariants. These results do not assume a callback relation.

`InternedRootProfileCleanup.smart_profile` proves that actual smart cleanup
has the fixed capture profile. Its premise relates the actual normalized
body profile to the pure callback probe profile. Actual source record
invariants and freshness of the allocated local discharge every cleanup
case. No independent self-filter premise is required. `opaque_finish`
proves that opaque body profiles stay opaque through cleanup.

The full nested source interpreter must still derive the body-profile
premise and the corresponding stored-cache invariant. These constructor
lemmas do not claim general first-run completion or Haskell-to-Lean
translation correctness.
