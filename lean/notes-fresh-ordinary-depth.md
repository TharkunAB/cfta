# Exact source normalization depth

Current extension: arbitrary-record source depth and completion are proved.
The actual optional-binder substitution now derives successful execution
without a prepared-body premise. See
[record completion](notes-record-depth-completion.md), checkpoint `e4a011e8`.
Earlier literal-only limits and next targets below are historical. The next
obligation is output preparation or a broader cold-reader invariant and
physical product rows. Native first-run success under checked words is
proved in [successful native execution](notes-native-successful.md).


Updated: 2026-10-14 11:28 CEST.

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

## General repaired source completion with literal inputs

`d2ebaddf` proves closed-source completion for arbitrary nested source syntax.
`ProbeChoiceSites.completed_scoped_route` retains the exact captured suffix at
every earlier crossing. Its previous public wrapper remains. The active
representative and earlier-pair theorems retain the same suffix evidence.
`JointMismatch.Mismatch` now keeps it with both actual earlier probes.

`RouteLevels.Path.projected_names` follows the actual current source path from
outer callbacks to inner callbacks. It derives projected-input agreement at
each nested ordinary call. `crossing_name` applies `callback_level` to those
actual completed probes. Depth/fresh choices have the same projection.
The ordinary choices therefore agree. No level equality is supplied.

`ClosedCompletion.site_impossible` contradicts the exact live ordinary
mismatch. Actual chronological growth and `DepthHeap.of_grows` recover the
needed decoded heaps from the final heap. `closed_not_pending` derives the
final heap from actual closed execution, including a hypothetical pending
outcome. `closed_complete` then derives a complete value and its exact final
cache for every source expression built from empty captures and caches.
No constructor termination contract, prepared-heap premise, or completed
source execution is supplied.

`f095aa16` extends this result. `literal_not_pending` and `literal_complete`
allow arbitrary literal captures and an arbitrary initial cache with a full
source context, decoded depth heap, and complete payload coverage. The empty
corollaries instantiate these conditions from the proved empty invariants.

## Next source obligation

Extend depth/deep observations, projected-level agreement, and completion to
mixed lexical inputs: a varying reference prefix and unchanged arbitrary
captured records. Native optional-binder substitution can capture complete Mu
records. It is outside the literal-input result. Keep each fixed record's
cached depth, roots, deep names, free names, and profile observations.
An opaque profile alone does not retain root alternatives of a mixed union.
Derive the input relation from actual available coherent records.

Then compose the general callback result with actual `maybeMu` and prove full
semantic-context and decoded-heap preservation on native prefixes. Initial
complete coverage alone does not supply those invariants. Use the existing
finite native return-or-pending theorem to derive successful first-run bounds.
Output preparation, or a broader cold-reader invariant, and physical product
row membership/rejection remain open. Universal preparation preservation at
all native sites remains refuted.

The retained producer-descent alternative has no second paired producer
observation. Literal-input completion uses route agreement instead. Do not
repeat the closed/literal proof or try to infer producer result liveness from
a descendant path.

The audit passes 1,332 jobs and 42,296 theorem dependency checks with only
`propext`, `Classical.choice`, and `Quot.sound`. Log:
`/tmp/mcfta-literal-completion-20261014-audit.log`.
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
