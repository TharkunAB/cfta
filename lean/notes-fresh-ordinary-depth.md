# Exact source normalization depth

Updated: 2026-10-13 17:05 CEST.

`InternedNormalizationDepthExact` proves exact cached depth equations for
the actual source normalizers. It applies to both constructor policies.
`makeNode_depth` gives the maximum depth of the canonical surviving edge
children. `makeUnion_depth` gives the maximum depth of the original input
records. `filter_depth` proves that root self-reference removal preserves
the complete input record's depth.

The lower bound uses `depth_witness`. Every available coherent value with
positive depth retains a Mu record of the same depth. Existing source
retention theorems keep that record through union flattening, identity
deduplication, ordinary edge merging, and self filtering. Existing upper
bounds then give equality. The union and filter statements require the
derived live-edge invariant. They do not assume a depth replay law.

`InternedFreshOrdinaryCallbackDepth.callback_depth` exposes the actual raw
body execution of each completed repaired callback. Its normalized result
has the same cached depth as that raw body. Thus callback depth variation
between different supplied names must come from body execution. The root
self filter cannot produce that variation.

This does not prove that all three repaired callback arguments return the
same depth. A general depth interpreter still needs the distinction between
root self alternatives and deeper free occurrences. The current free-name
interpreter counts both. Root self filtering can remove a bare local from
an opaque union while retaining all deeper occurrences. Raw `usesArgument`
therefore does not determine whether smart cleanup keeps the binder.

Focused finite searches in a separate Python mirror found no repaired
pending request in 320 marker/depth/wrapper cases or 2,512 cases with
discarded marker and child effects. A later search checked every stored Mu
in 30,000 completed closed executions. It found no difference between the
actual body depth and the stored Depth probe depth. These searches did not
skip cases for resource limits. They are diagnostic evidence only. Their
scripts are `/tmp/mcfta-fresh-repair-search-wide.py`,
`/tmp/mcfta-fresh-repair-hidden-search.py`, and
`/tmp/mcfta-fresh-repair-depth-search.py`. The old executor and its checked
depth mismatch and pending examples remain unchanged.

The two new proof modules build with Lean 4.34.1 in 185 jobs. The focused
audit checks 7,959 theorem dependencies and permits only `propext`,
`Classical.choice`, and `Quot.sound`. The log is
`/tmp/mcfta-fresh-ordinary-depth-audit.log`.
