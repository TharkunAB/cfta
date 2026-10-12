# Final finite observation merging

`FinalObservationRanks.lean` and `FinalObservationMass.lean` extend
`OpenGroupedApplication.lean` through the final observation partition and
`ungroup`. They contain executable selectors, callbacks, merge operations,
error gates, and rational distribution operations. They do not assume that
the whole compiler preserves a language or a distribution.

## Source operations

The rank model follows these operations:

- `Static.pointsStatic`: split the member rank into an original rank and a
  point rank. Select the original private term. Apply the parent label and
  fill its coordinates. Query the original callbacks, extract coordinates,
  invert the lattice point, and check the complete requested view.
- `Static.frequencyStatic`: add a local `Choice` index. Select the branch by
  cumulative member counts. Keep the child rank within that interval.
  Whole and spine queries require the corresponding private wrapper.
  Labelled queries visit every branch.
- `Bucket.mergeBucketGroup`: keep a positive singleton unchanged. A larger
  group uses frequency construction. `integerOutcomes` rejects empty inputs
  and nonpositive outer masses. Integer conversion preserves all normalized
  branch weights through `Sampler.integerMasses_normalize`.
- `Bucket.mergeComponentsByKey`: partition components by observation key,
  merge each partition, and divide all outer masses by their accepted total.
- `Grouped.regroupOn`: partition the ordered bucket entries, merge each
  group, and clear its inspection name. The name update does not change
  terms, ranks, counts, or masses.
- `Grouped.ungroup`: regroup at the unit key and return that bucket.
  `unit_group` and `ungroup_source` prove the exact one-bucket order.

The finite map is represented by its ordered entry list. The caller supplies
the key projection and key comparator. The proofs hold for every such
partition. They do not assume that distinct observation keys have disjoint
decoded values. `GroupPositions` supplies the separate source position-table
lookup invariants.

## Derived initial records

`pointIndex_exact` derives the initial replay and callback invariant from
`OpenGroupedApplication.Source`. That source contains actual generated,
repeated-key, and applicative `JoinN` constructors. The proof uses their
selectors, candidate discovery, hole counts, and the successful public
lattice query. It does not assume a term-codec inverse.

`settledIndex_exact` uses the actual settlement success and
`IntegerLabelCodec.exactLabel_matches`. `settledBucket_valid` also derives
the conditional probability, member count, and positive retained outer mass.
It obtains the latter from the actual child tables, stored child counts, and
the successful nonempty parent table. It does not assume that the computed
retained share is positive.

The initial distribution records provenance as the original group identity,
the original member rank, and the decoded integer tuple. Its weights are the
actual original-rank weights times uniform retained-point weights. The outer
mass is the source bucket mass times the computed retained share.
`settledBucket_raw` connects this record directly to
`OpenGroupedApplication.closedDistribution`. A predicate on provenance can
inspect any resulting deterministic value. Duplicate values retain the sum
of their member masses.

## Nested merge results

`frequencyRanks_exact` proves sound and complete callbacks in all three
views. `selectBranches_member` and `mergeIndex_member` derive the precise
private wrapper and rank offset of every retained input occurrence. The
positive singleton path omits the wrapper. `branch_intervals_disjoint`
proves that different branches occupy disjoint rank intervals.

`merged_rank_record` relates the term selector and weight field at the same
rank. For a non-singleton merge, a child member with conditional mass `p`
gets mass `bucketMass / totalBucketMass * p`. The offset uses member counts,
not these weights.

`merge_restore` reconstructs the complete unnormalized input stream from
the merged outer mass and conditional stream. `regroup_raw` proves that
observation grouping retains every weighted occurrence, up to map order.
`normalize_raw` proves that source outer normalization applies one common
scale. These laws compose through nested frequency wrappers.

The final results are:

- `checkedResult_success`: every nonempty constructor-valid finite family
  reaches the executable final record. `checkedResult_empty` keeps
  `EmptyGenerator` as an error.
- `result_interval`: the final selector succeeds at exactly the sum of all
  incoming original-times-point counts. It has no missing or extra indices.
- `result_ranks`: each view query returns all and only the replay positions
  with that view.
- `result_distribution`: the final conditional distribution equals the
  normalized sum of retained input contributions for every event.
- `result_valid`: these rank, count, probability, and positive-mass
  invariants remain available for a later finite merge.

## Boundaries

This result covers the finite integer `closePoints` path and its subsequent
observation merges. It does not extract the entire `compileGen` implementation
into Lean. Its initial finite child tables and stored point records come from
the previous constructor proofs. Successful label specialization remains
explicit because the source wrapper can raise a checked substitution error.
The zero-width fast path has separate metadata proofs in
`ParentIntegerSettlement`; arbitrary imported and recursive records are not
new seed constructors here.

The record model includes global member masses. It does not add a new joint
proof for every size-index, shrink, sampler, and inspection field. Existing
size-mass proofs remain separate. `frequencyStaticWithMasses` changes the
size-conditioned sampler; it retains the global frequency selector and mass
law modeled here.

The rank interval indexes member occurrences. Parent labelling can erase
private choices. Distinct members can then have the same whole or labelled
term, or the same value. The proofs preserve every such preimage. They do not
claim that this member index is the distinct-term index of an arbitrary
FTA. The distinct-language construction remains a separate specification.

## Validation

Both modules build with the repository's pinned Lean 4.34.1. The final build
has 98 jobs and 58 new theorems. There are no `sorry`, new axioms, or native
decision proofs. No production Haskell file changed. The existing 618-test
Haskell result was not rerun because this step changed only proofs and this
note.
