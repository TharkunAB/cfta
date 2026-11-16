# Actual compatibility producer

Status: source audit, not a proved history theorem.

For fixed final `rho`, a repeated child position must have one target term.
If both occurrences hold at the same parent, their `atPath [position]` results
are equal. `Option.some` injectivity gives equality of the target terms. This
condition is necessary. The new local constructor shows it is sufficient for
an arrow parent under the stated path, type, separation, and UF conditions.
Left and right positions need not have equal terms. An occurrence present at
both positions requires its one actual target term at both positions.

The exact stronger source conclusion that would discharge term compatibility is:

```
forall (firstIndex secondIndex : Nat) (first second : Suspended) (position : Nat),
  removedBucket[firstIndex]? = some first ->
  removedBucket[secondIndex]? = some second ->
  [position] in EqualityTrie.fromPathTrie first.trie ->
  [position] in EqualityTrie.fromPathTrie second.trie ->
  UnionFind.SameClass final.core.representatives first.var second.var
```

This is a desired actual-source conclusion. It is not a new permitted global
premise. Final UF consistency would then yield the new local compatibility
input for the SAME actual final assignment.

The existing `SourcePruningEnumerationSharedPreparedRawPathCongruence.actual_prepared_child_raw_path_congruence`
at line 19 produces exactly these raw aliases at an actual successful shared
child return. It retains the literal parent bucket, both duplicate indices,
actual prepared child position, valid tries, and actual ChildDispatch result.
It assumes a real traversal. The genuine terminal child producer is
`ChildDispatch.terminal_singleton_final_raw_target_incidence` at line 145 in
`SourcePruningEnumerationSharedChildFinalRawTargets.lean`.

Two missing links prevent using that result for an arbitrary later removed
bucket. The exact removed occurrence pair must originate in that processed
parent bucket on the SAME emitted branch, with its raw IDs and positions.
The aliases must then reach the SAME final UF snapshot. Actual frame receipts
can transport aliases where their endpoints align. The held-class preservation
in original906 alone is not arbitrary two-target alias transport.

`parked_singleton_removed_bucket_receipt` at line 72 retains the actual removed
full bucket and key membership. `enter_recorded_bucket_origin` at line 17
retains one actual entry's full bucket. `prepared_terminal_child_written_path_origins`
at line 62 retains ordered write occurrences from parent descent, fresh own
suspension, or an old bucket. These are genuine local producers. They do not
yet derive the complete removed-pair-to-earlier-child connection.

`EnumerationState.recursionKey` at line 62 discards raw variable IDs, occurrence
multiplicity, and order. Equal keys or tries cannot discharge those missing
links. A repetition-skipped child has no new ChildDispatch traversal to use.
No reachable counterexample or Haskell defect is claimed.

The used-target TypeIn premise also needs a source producer at the final rho.
Current assignment results make every directly pending slot var1. Historical
raw targets can now be expanded. Their actual final terms need their own source
type qualification. Do not substitute the pending-only guarantee.
