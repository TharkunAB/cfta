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

The functional array model specifies source reads and writes. Physical
`STUArray` storage and machine bounds remain representation contracts. The
complete class-iteration and output-grouping loop still requires a caller
proof. The primitive array proof does not assume that loop computes the
connected components.
