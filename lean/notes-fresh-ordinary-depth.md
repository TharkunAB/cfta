# Exact source normalization depth

Updated: 2026-10-14 11:12 CEST.

## Current full source depth and level comparison

`42ce3d8a` completes the depth/deep heap induction for arbitrary nested source
syntax with literal lexical inputs, `names.map Value.reference`.
`InternedFreshOrdinarySourceDepth.build_depth`, `buildMany_depth`, and
`buildEdges_depth` follow actual ordered execution through nodes, unions,
and both binder forms. Every outcome retains the decoded heap. Every return
has the independent pure interpreter's emptiness, cached Mu depth, and deep
names. No recursive body-depth or deep-observation contract is supplied.

`InternedNormalizationDepthExact` now removes canonical edge order and
deduplication from the maximum-depth equation. The surviving original edges
have the same maximum. `InternedFreshOrdinaryDepthComposition` composes
ordered observations, actual edge deletion, union normalization, callback
filtering, and both actual probes. The two probes determine raw and smart
binder depth and deep names. Existing independent free/profile heap results
remain part of the incoming source context.

`callback_depth` derives the normalized callback's complete depth and deep
response. `arguments_depth` proves equal actual cached depth for any two
supplied names with the same literal captures, valid source contexts, and
decoded heaps. `closed_heap` derives that heap from empty caches even for a
pending outcome. `closed_observed` derives the complete returned observation.
`InternedFreshOrdinaryDepthHeap.of_grows` recovers an earlier decoded heap
from actual retention in a later decoded heap.

`d0083f37` adds `InternedFreshOrdinaryLevelReplay.callback_level`.
`ordinaryNames` retains `.uninterned level` and maps every other reference
kind to `.depth`. Equal projected literal capture lists determine equal
actual repaired ordinary levels for two completed Depth callbacks of the
same source body. The proof derives both cached-depth equality and equality
of the ordinary free-name bounds. It does not assume either equality.
The pure literal free-name transport theorem is reused. The actual callback
proof uses the repaired executor.

## Next source obligation

Retain exact captured suffixes at all corresponding earlier and current
route crossings. `ProbeChoiceSites.completed_route` currently returns actual
crossings, descriptors, contexts, and cache histories, but its conclusion
drops the capture relation at each earlier crossing. Strengthen that result
and preserve its current public wrapper. Derive the corresponding relation
from the actual current `ActiveOrigins.Path`.

Then apply `callback_level` from outer crossings to inner crossings.
Corresponding Depth/fresh choices have the same ordinary-name projection.
Corresponding ordinary choices need equal projected captures and decoded
heaps at their actual starts. Recover the heaps from `closed_heap` and
`of_grows` using actual source growth. Establish the route invariant before
claiming that the live ordinary mismatch is impossible. Do not assume equal
levels from cached depth alone.

The retained shorter-producer descent is another possible route. Its second
paired producer observation remains open. The new level theorem does not
supply that observation or general pending exclusion. Arbitrary captured
records in native optional-binder calls are outside the literal-input driver.
Full incoming native semantic-context preservation also remains open.

The audit passes 1,330 jobs and 42,279 theorem dependency checks with only
`propext`, `Classical.choice`, and `Quot.sound`. Log:
`/tmp/mcfta-level-replay-20261014-audit.log`.
A 45-second targeted mirror search completed 7,541 repaired cases with no
pending read. Another 198 cases hit resource limits. This is diagnostic
evidence, not a completion proof. Script and log:
`/tmp/mcfta-repaired-pending-producer-search-20261014.py` and `.log`.

## Earlier normalization checkpoint

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
