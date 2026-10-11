# Finite structural shrinking

`MicroCFTA.Shrink` models the rank and size structure read by
`Data.CFTA.Ranked.Internal.Shrink`. It includes every finite constructor:
select, select-on-demand, pure, pay, shared, map, choice, application, and sized.
Values do not affect the shrink decisions. Choices use the same offsets.
Applications use the same quotient and remainder. `halves` and `towardZero`
implement the integral shrink sequence. A list of choice alternatives becomes
right-associated binary choices.

`smallest_correct` proves that the computed minimum has minimum size. It also
proves that this member has the least rank when sizes are equal. The theorem
derives these properties from the recursive algorithm.

`shrink_safe` proves that each structural candidate has a smaller rank and a
size no greater than the starting member. `shrink_valid` keeps each candidate
in the rank interval. `no_infinite_shrink_chain` proves termination from one
valid starting rank.

`sizeDecoder_count` and `sizeDecoder_correct` connect the size projection to
the independent decoder semantics. `mem_classRanks` and `classRanks_nodup`
prove that each size class contains exactly its member ranks, once each.
`mem_smallerMembers`, `smallerMembers_nodup`, and `smallerMembers_ordered`
prove complete, unique, size-ordered coverage of all smaller members.
`exhausted_smaller_search` states the minimum-failing-size consequence when
the complete smaller-size stream has passed the property. A capped search
does not satisfy that premise merely because it reached its cap.

## Representation boundary

Counts and application radices are derived from the child plans. Sized members
carry a proof of nondecreasing size. The source documents these requirements
on `PlanChoice`, `PlanAp`, and `PlanSized`; it does not check arbitrary malformed
internal plans. Shared nodes use their inner plan. The Haskell shared decoder
and size cache must agree with that plan, as the source requires. Cache storage,
source callback totality, and arbitrary invalid Haskell metadata are outside
this model. The size decoder does not prove properties of arbitrary decoded
values. These are explicit representation obligations, not assumed shrink
postconditions.

The stream uses all sizes below the current size and omits empty classes.
The source uses its ordered sparse size table. Their class membership and
product split order agree under the size-index invariants. The proof does not
measure laziness, allocation, or time to select a class member.

## Source check

A temporary comparison ran in `nix-shell` on 7,504 finite Haskell plans.
The plans included empty sources, zero-size members, zero-count size classes,
select-on-demand, maps, pays, shared plans with derived caches, choices, and
products. For every valid rank it checked the smallest member against a brute
minimum, strict rank decrease, non-growing size, exact smaller-size coverage,
and stream size order. All checks passed. The probe is
`/tmp/microcfta-shrink-check.hs`; no regression test was added.
