# Runtime bound for projected leaf equality passes

`EqualityLeafProjectionRuntimeBound.compiled_bound` proves termination of a
fixed normalized equality schedule on finite ordinary occurrence forests
whose selected endpoints are leaf domains. The bound is the original
`forestWeight rank` plus one passes. The theorem includes noncanonical
initial residual guards, duplicate ancestor rows, dead rows, absent child
positions, and global empty propagation.

The source class reads every target from one original physical forest.
Each target excludes its own path and uses the first other projection as
the seed of the right intersection fold. The class then applies simultaneous
physical targets. Classes execute in the source right-fold order. The pass
keeps the skip, contradiction, required-path, schedule, and empty-propagation
branches in that order.

`RuntimePass.pass_progress` constructs an exact occurrence witness for the
actual output cache of every pass. Raw leaf pullback reconstructs admitted
leaf rows directly in that cache. Trimming removes hidden dead occurrence
requests before reconstructing parents. This is necessary: a proof-prepared
cache can allocate identities that conflict with a later independent runtime
allocation. The proof never starts a runtime pass from that prepared cache.

`RuntimeTermination.iterate_completes` tests the ordered physical reference
list after each pass. A changed list forces a strict natural-weight decrease.
An unchanged list gives equal complete records in the coherent runtime
cache. The final pass then replays without allocation. This proves a physical
fixed point, not only equality of interpreted row sets.

`ProperPaths.normalized_proper` derives nonempty selected paths from completed
source normalization. A nontrivial class containing the root path would
contain a strict-prefix contradiction. Reordering and filtering normalized
classes preserve this property. Raw public constraint constructors still
need their explicit well-formedness conditions.

The source correspondence checks include node-identity operand orientation
before the Cartesian intersection, allocation-free empty intersections,
and the equal-arity `setChildren` shortcut. The path worker directly uses
the ordinary `Operations.union` branch. `EqualityOrdinaryUnionSource.union_run`
proves that this branch and constructor union have identical complete runs
on the represented ordinary operands used by the leaf proof.

`EqualityLeafProjectionOrdinaryMetadata` derives zero Mu depth and an empty
free-reference list for every represented ordinary record. These are the
source recursion-filter fast-path fields. They also justify the closed
self-intersection shortcut. The fixed ordinary fragment cannot change its
class eligibility through recursive unfolding.

The theorem does not cover an equality endpoint with nested children.
Intersection at such an endpoint can create new ancestor alternatives.
It also does not cover changing class eligibility through recursive
unfolding or repeated recursive child reductions. The bound counts passes.
It does not bound per-pass work or total cache allocation. The physical
model retains the existing host-container, identity-lifetime, and Haskell
execution contracts. It is not compiler extraction or a proof of host
evaluation order.
