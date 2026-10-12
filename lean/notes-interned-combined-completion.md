# Mixed completion from actual earlier source traces

`InternedNestedTraceSites.Site` identifies an expression's source position
and counts the binders crossed to reach it. `completed_site` extracts an
actual completed execution at that position from a completed enclosing
execution. Under each crossed binder it uses the source depth callback.
It proves the exact earlier and later cache-growth relations. The proof
includes children in discarded edges and bodies of cached binder calls,
because the source still executes their probes. `site_replay` derives later
replay when the original input slots agree.

`InternedNestedInputScope.closed_inputs` derives an empty input inventory
from `Scoped 0`. `InternedNestedPreparedSites.ready_from_trace` then prepares
every closed descendant for exact replay at later states. `Ready` is an
intermediate proof property. The public completion theorem does not assume
it. A real completed depth-body trace establishes it before reservation.

`InternedCombinedConstruction.Combined` places three mechanisms in one
source grammar. Ordinary node and union children can contain retained
binders or closed subprograms. Retained binders declare the enclosing
reference edges from `InternedRetainedConstruction`. Closed subprograms
have either the independent `Staged` condition or the erased-body `Admitted`
condition. These checks use the original source syntax.

`InternedCombinedCompletion.build_completes` follows the actual source
schedule with its exact pending frames. A closed subprogram's first call
uses the existing first-completion theorem while no ancestor is pending.
If an ancestor is pending, the source position selects its earlier complete
result from a real depth trace. The new fresh callback derives its prepared
sites from that depth trace before entering the body. The ordinary probe
and all later child and edge effects preserve those complete requests.
The retained-reference argument excludes the remaining pending-key aliases.

`closed_completes` starts with empty caches and an empty pending context.
`closed_complete_record` adds complete payload coverage, actual record
provenance, an available result, and exact subsequent whole-program replay.
Neither public theorem assumes callback stability, source-site readiness,
probe residency, or a successful first run. `mixed_complete` checks one
closed program with retained ancestors and both kinds of closed subprogram
in their nested child positions. `mixed_scoped` checks its lexical closure.

This theorem combines the fragments inside pending source executions. It
does not prove completion for every closed expression. A nonclosed nested
call can retain one ancestor and erase or ignore another. Its later local
identities can differ from those in the earlier depth trace. The current
combined rule requires dedicated retention of every enclosing slot or a
fully closed subprogram. General normalization and trace correspondence
for that remaining mixed dependency case is still open.

A temporary executable-model search checked 114770 closed terms and found
no pending readback. It skipped 1556 terms after a resource limit. This
diagnostic is neither a source implementation test nor a proof of general
completion. No committed test or source implementation change is included.
