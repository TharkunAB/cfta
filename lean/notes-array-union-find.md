# Equality completion parent-array refinement

`ArrayUnionFind` follows the local `find` and `union` workers in
`Equality.Constraint.normalize.complete`. The source stores each root as its
own parent. It links the left root to the right root without comparing sizes.
This differs from the enumeration union-find's union-by-size choice.

`erase` removes ghost root sizes from the proved forest representation.
`find_refines` connects complete path compression to the actual parent reads
and writes. `erase_link` reduces the ghost link operation to the source's
single parent write. `unionLeft_correct` proves that this unweighted link
merges exactly the selected two classes. `union_refines` connects both source
lookups and the link to the concrete array worker. `union_terminates_exact`
derives finite termination and exact class changes. `initial_array` proves the
source singleton initialization has this representation.

`EqualityArray` verifies the caller. `classPairs_exact` proves the source's
first-member star represents the whole class. `mergePairs_correct` composes
all unions. `readAll_correct` proves representative readback preserves the
partition and records exactly the requested members. `grouped_partition`
proves the root buckets represent that partition. `complete_connected`
derives the exact independent connected relation. `complete_groups_exact`
retains exactly all original assignment equations.

`mergeArrays_refines` and `readArrays_refines` compose actual array operations.
`complete_terminates_exact` derives finite bounds for the whole algorithm and
its exact output equations. No caller-level connected-component property is
assumed. Group ordering has no effect on these equations.

`ArrayBounds` proves that initialized parents stay in the allocated interval.
Find, union, all merge iterations, and representative readback preserve these
bounds. Returned representatives are allocated. Input path indexes must come
from the source's finite member map.

The functional array model specifies source reads and writes. Physical
`STUArray` storage and conversion of the finite size to `Int` remain contracts. The
path-to-index map, inverse path lookup, canonical output ordering, and their
composition with the saturation loop remain source adapters. The existing
`EqualityNormalize.complete_matches_partition` states the canonical
connected-partition uniqueness property needed by that final composition.
