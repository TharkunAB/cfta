# Finite generator composition

`MicroCFTA/GeneratorCombinators.lean` models the finite member operations in
`Gen.Internal.Static`, `Bucket`, `Grouped`, `Join`, `Chain`, and `Query`.
The source base is `origin/microcfta` at `d7f7c11`.
Members retain an engine term, a value, a FEAT size, and rational mass.
Lists retain rank order and repeated values. These ranks index members.
They do not identify equal values or equal user terms.

`indexed_count` counts input positions. `member_has_rank` gives every stored
member a valid replay position. `pair_count` derives the product count.
`pair_select` proves the actual quotient/remainder selection order.
`pair_values` proves independent product probabilities. Products add sizes.
Map, pay, and atomic boundaries preserve the output distribution.
Pay increases sizes by one. Atomic boundaries assign size one.

`frequency_values` preserves each branch's internal distribution and uses
the supplied branch weights. `uniformly` supplies branch cardinalities.
`uniformly_value_mass` checks the difference between branch weighting and
member weighting. `uniformly_keeps_branch_weights` shows that cardinality
weighting does not replace an internally weighted branch with a uniform one.
Thus the name `uniformly` does not imply uniform decoded values.

`groupOutcomes` partitions by key and sorts the keys. `prepareGroups` also
sorts each group by member size. `prepareGroups_perm` proves that all
weighted members remain. `prepared_key` derives the common key of each
group. `grouped_relation_filter` proves that testing a relation once per
key pair gives exactly the matching member pairs. `groupProducts_perm`
proves complete weighted product coverage. `join_event` proves that the
normalized join has the original product distribution conditioned on its
key relation. `joinTerm_keys_equal` verifies the private group-label terms
at the source equality paths `[0,0]` and `[1,0]`.

`bucketFromOutcomes` stores the original group mass and conditional members.
`bucket_count` retains all positions. `bucket_restore_values` proves that
the stored mass restores all original output masses. `bucket_size` records
the source's size-one `PlanSelect`; grouping does not generally retain the
input plan's sizes. `bucketMassIndex` uses a retained mass table when one
exists. Otherwise it uses member counts. This fallback does not inspect
outcome probabilities. `SizeMass` separately verifies the size-class mass
algebra and includes the unequal atomic-weight fallback counterexample.
The size reset is documented public `groupOn` behavior, not a defect.
`Grouped.hs` states: "Every member of a group has size one."
`regroupOn` merges existing buckets without enumerating them again.

`enumeratedRanks_exact` proves that the finite inverse query returns every
rank whose term satisfies the supplied view predicate. It includes every
occurrence of an equal term. `enumeratedRanks_nodup` proves that it repeats
no rank. The source uses this operation for enumerated leaf callbacks.

The model derives counts, distributions, and key coverage from executable
operations. It does not assume their desired postconditions. The source's
`Map` and `Seq` adapters, stable-sort implementation, term-view predicate,
checked-symbol shortcut, and stored callback fields still require their
representation correspondence. Key comparison must implement the source's
lawful `Ord` order. The permutation and distribution proofs do not require
an order law; exact source rank order does. The binary product law supports
iterated chains, but this file does not port the heterogeneous `Args` GADT
or its signature wiring. Recursive joins and lazy size streams use the
separate recursive models. Error dispatch, opaque sources, backend draws,
and user effects remain separate API operations.

Validation: `lake env lean MicroCFTA/GeneratorCombinators.lean` succeeds with
the pinned Lean toolchain. No `sorry` or additional axioms are used.
