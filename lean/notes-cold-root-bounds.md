# Complete cold-root group bounds

`MergedColdMergeRootBounds.worker_root_bound` proves that every successful
closed ordinary worker returns at most four rows for each symbol/arity key.
The proof follows the actual returned rows and cache. It does not infer the
whole-root bound from unrelated local group counts.

`MergedColdMergeMapFacts.map_valid` composes successful callbacks in their
actual state order. It retains the input/output positions, source facts,
and result availability. `worker_valid` derives the recursive callback
certificate from the complete cold worker.

The small-edge proof keeps the original symbol and exact child count. The
large-edge proof derives the child count from source transpose and the
actual completed column map. The group proof retains these keys and the
literal four-row threshold. `MergedGroupPartitionBound` derives distinct
source groups from executable partitioning. `MergedNodeRowBounds` proves
that canonicalization, duplicate removal, and empty-child removal cannot
increase any selected row count. Actual node-cache readback is included.

`root_permutation_bound` permits arbitrary hash-table bucket order. Its only
ordering premise is a permutation of the derived source buckets. It keeps
the required order inside each bucket. `root_trace` retains the exact final
node request over the complete certified row groups.

`root_normal` and `worker_root_normal` prove exact reconstruction of the
returned root from its own outgoing rows. They use the actual source node
constructor. They do not assume that every arbitrary coherent input is
already canonical. Recursive normalization and fixed-point termination
need additional child and schedule arguments.

The initial source facts, prepared Mu fragment, and input availability
retain their existing scope. The model does not replace the source hash
table with a verified native container implementation.
