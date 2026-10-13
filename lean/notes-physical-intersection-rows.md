# Physical intersection, recursive exposure, and shared-row productivity

`SourceInternedIntersectionRows*` executes the ordinary plain construction
kernel. It follows the symbol hash join, reversed right bucket order, arity
check, ordered child calls, edge interning, surviving-row filter, and canonical
node construction. Cache hits retain the complete recorded payload.
A concrete left-record size bound derives recursive correctness and finite
completion. The result has the exact common language in the physical epsilon
graph. Additional fuel preserves both output and final cache.

`SourceInternedIntersectionDispatch*` adds actual empty, closed-self, and
sorted-operand control. Both record sizes bound the recursive dispatcher.
It derives the public empty-domain decision, reset/swap conditions, and the
completed recursive caller equation. The closed-self branch obtains record
equality from cache identity coherence.

Completed memo entries carry concrete dispatcher execution provenance.
`nativeRun_correct` derives their semantic result from that execution.
`native_flat_insert` connects ordered native keys, issued-word bounds, and
physical flat-table insertion. These proofs do not assume arbitrary compute
purity. They cover completed values. Native pending-thunk publication,
blackholing, and the complete recursive memo-effect trace remain outside
this model. Swapping operands re-enters memoization under a reversed key;
constructor-effect stability does not identify those memo traces.

`SourcePhysicalSharedRows*` reads the actual issued node cache and complete
resident records. Cache facts, availability, and plainness derive exact
ordered row exposure. `collectValues` visits actual pending Value payloads;
`collect_readback` relates it to the shared map worklist. The issued counter
derives a finite traversal and stable row result.

`language_exact` and `minimum_exact` derive the physical/shared language and
least accepted node count. `productive_source` includes the actual empty-row
precheck. `native_callback` builds completed rows and minimum sweeps for the
actual native dispatcher result. It proves that productivity is equivalent
to a shared original term. No `ProductRows`, global child-meet assignment,
copied-row premise, or assumed language equivalence remains for this finite
plain callback.

`SourcePhysicalRecursiveRows*` now proves the single-knot fragment
`mu x. (base | step x)`. Actual repaired unfolding performs two `makeEdge`
requests and one `makeNode` request. The proof retains their exact returned
cache, resident records, availability, and original Mu child. It derives
stable replay without allocation and an independent language of finite Chain
terms. `shared_exposure` derives finite shared traversal and exact original
language from the actual exposed rows.

The recursive proof starts from an available coherent stored knot. It does
not yet provide a construction witness for that premise. General Mu/union
exposure and pending-thunk execution remain open.
`InternedDepthFreeProjection*` separately derives full-syntax free-name
membership and ordinary-root deep callback observations, including nested
children. General cached-depth and binder-heap induction remain open.

Checkpoints: `70795677`, `0bc6806e`, `aca84882`, `7e942dde`, and `9207c2cf`.
The closing audit passes 1,180 targets and 39,689 theorem dependency checks.
Log: `/tmp/mcfta-closing-20261014-audit.log`.
