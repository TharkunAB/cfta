# Recursive physical workers for projected leaf paths

`EqualityLeafProjectionWorkers` copies the finite ordinary branches of the
source path operations into actual `Work` computations. A selected parent
maps its original ordered children and then calls `makeEdge` and `makeNode`.
The edge key keeps the source symbol and complete constraint. Required-path
filtering rejects rows with a missing original child before child recursion.
Unselected positions and empty requirement tries return their original
records. EmptyNode returns immediately without allocation.

A visited binder, free reference, or open union returns `none`. This result
marks the boundary of the finite ordinary fragment. It does not model the
source's recursive unfolding behavior. Unselected recursive positions can
return unchanged. The theorem premises use ordinary records throughout the
finite input, so selected unsupported constructors cannot occur.

`EqualityLeafProjectionWorkerCompletion` proves that the workers complete on
every finite ordinary input. It does not assume their completion. An edit's
leaf intersection is a finite supplied `Work` computation; its constructor
safety is explicit. The worker proofs derive record coherence and cache
growth after completion. The required-path worker has no supplied operation
or completion contract.

`EqualityLeafProjectionReplay` enumerates the original child occurrences and
executes their finite physical requests. The resulting common cache replays
every request with its exact value and no new allocation. The ordinary-input
proof establishes a successful option result. Thus the default in the total
`workerValue` accessor is unreachable for these represented requests.

`edited_parent_completed` and `required_parent_completed` use this generated
cache and the actual returned recursive child results. They then execute the
parent edge requests and derive exact normalization against the source's
stored canonical edge list. These results remove the earlier supplied child
transformation, empty-node law, and output-residency premises. Empty-node
preservation follows directly from the worker equations.

The comparison uses a common completed cache and preserves complete source
records. It does not claim equal allocation traces when retained provenance
rows cause additional recursive or dead-edge requests. The required-path
proof executes child requests only for rows that pass the arity filter; its
proof-only parent completion can also prepare records for discarded original
rows before the final filter.

The remaining adapter work connects physical leaf intersection and physical
projection union to the abstract leaf row representation. It must then
assemble the stateful recursive worker results into the pure source
constructor/read interface used by the fixed-point bound. The new worker
proofs do not by themselves remove every premise from that interface.
