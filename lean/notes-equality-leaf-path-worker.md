# Physical ordinary path projection

`EqualityLeafProjectionPathWorker` copies the ordinary `getPath` branches
from `Data.CFTA.Interned.Operations`. A proper path selects the indexed
child of every stored edge. Missing positions issue no child request. The
worker makes one source union from the returned projection list. It keeps
the actual canonical edge order. Forest root projection unions the entire
forest. Forest child projection returns EmptyNode for an absent position.

`read_safe` derives complete-key request safety. `read_returns` proves
completion on every finite ordinary input. `read_available` derives full
cache facts and complete result availability. The optional failure branch
records an unsupported recursive or open union root. The ordinary input
proof excludes that branch; this module does not model recursive unfolding.

`EqualityLeafProjectionPathInputs` derives selected child representations
from original occurrence endpoints. `PathTransport` follows actual closed
row requests. `PathExact` proves that every leaf endpoint projects to a
finite raw leaf with exactly the returned complete record. Missing paths
return the empty leaf. No read law is supplied by the caller.

`EqualityLeafProjectionTargetFold` copies the source's first-seeded right
fold of physical intersection operands. It derives exact finite-carrier
correspondence, including the empty list and singleton shortcut.

`EqualityRawLeafPullback` removes temporary proof-cache preparation. Every
finite leaf row passes source admission. Its key must therefore occur in
the returned node. Residency of that complete node forces every requested
row and its parent constructor to be cache hits in the runtime cache.
The proof needs no common extension of divergent caches.

`EqualityLeafProjectionRuntimeLeaves` applies this result to actual endpoint
reads and target folds. Their finite representations replay in the actual
output cache. A subsequent runtime operation uses that cache directly.
`EqualityOrdinaryUnionSource` proves exact equality between constructor union
and the source ordinary `Operations.union` branch on represented inputs.
The path worker now calls that source branch directly.

Complete class, pass, and repeated-runtime composition is proved in
`EqualityLeafProjectionRuntimeBound`. See [the runtime bound](notes-equality-leaf-runtime-bound.md).
