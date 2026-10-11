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
`EqualityIndex` proves the complete path-index map and its inverse. Every
input path has exactly one valid index. Every allocated index represents an
input path. `indexed_exact` verifies the actual consecutive index entries.
`source_path_semantics` connects the complete indexed loop to existing-subterm
equality, including path existence. `source_canonical_semantics` includes path
set construction and final sorting.

`STUArray` storage and conversion of the finite size to `Int` remain contracts.
`EqualityPartition` proves the exact reference connected relation, disjoint
output components, and preservation of nontrivial classes.
`source_complete_eq` derives equality of the entire canonical output with
`EqualityNormalize.complete`. `completeArray_eventual` includes the concrete
array merge and readback workers. At every sufficiently large bound, they
return exactly that reference result. The repeated saturation proofs can use
this result at each active completion call. Source `Map`/`Set` operations must
implement their stated ordered-map and ordered-set contracts.

`EqualitySource` composes the full source initialization and fixed-point loop
with actual array completion at every step. `source_normalization_exact`
derives a sufficient execution bound and exact existing-subterm equality
semantics. `source_rejection_exact` proves that source rejection is equivalent
to having no finite equality model. The bound is proof instrumentation.
The Haskell loop runs until contradiction or canonical equality.
