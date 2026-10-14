# Native output scope and general repaired cold-reader effects

Updated: 2026-10-14 15:49 CEST. Latest proof checkpoint: `b3008aba`.
Native heap checkpoint: `9a0df4cb`. Earlier replay and counterexample checkpoints remain.

## Derived recursive scope

`SourceRecursiveIntersectionResultScope.Scope` permits only intersection
references from the incoming domain's seen pairs. Actual node and union
normalization retain child scope. A repeated pair is in the incoming domain.
A self return is closed because it passed the actual free-name guards.
The Mu body call uses the actual extended domain. Actual `maybeMu` removes
that selected pair from every returned free name.

`ScopeEffects`, `ScopeCalls`, and `ScopeRows` follow the exact source calls,
ordered walks, rows, references, and cache effects. `KernelScope.execute_scoped`
uses fuel induction over every source branch. Successful source returns
derive scope without an input preparation or output language premise.

`NativeResultScope.Meaning.request_scope` extracts actual completed source
execution from the exact guarded native meaning. The value and returned
machine are identical. `done_closed_of_ranges` uses the empty initial domain
to derive closed native output under the existing checked-word scope.
`cold_node_complete_closed` retains successful stable first execution.

## Original payload syntax

`OriginalOutput.original_of_free` follows coherent available record fields.
Every non-interned payload reference would propagate to the root free list.
A Mu removes only its own interned name. `closed_original` therefore derives
the existing `InputView.Original` predicate from closed available output.
`done_original_of_ranges` applies this result to actual native returns.
Probe metadata remains outside that predicate. The theorem does not claim
that all stored probe values have original payload syntax.

## General repaired reader effects

`MergedFreshOrdinaryColdEffects.collect_verified` follows the actual repaired
ordered worklist at every bound. Each actual single unfolding completes in
the retained semantic cache. Its result is available and closed. The proof
composes exact physical growth and issued history through later reads.
Ordinary rows remain resident and their children remain closed. Canonical
edge ordering retains those properties.

`nodeEdges_verified` covers direct node reads, the initial Mu fast path,
and the repaired closure fallback. Every outcome retains complete semantic
heaps and `Covered []`. It is done or exhausted. Pending constructors and
unresolved references are excluded. There is no preparation or `NoNewMu`
premise. Unfolding can allocate further Mu records.

`SourceRecursiveIntersectionNativeColdEffects.cold_node_read_effects`
derives successful stable native execution, closed original output, and
this reader invariant at every bound in the exact returned native cache.
It keeps the existing complete initial cache, closed Original input, and
checked-word scope. It assumes no output preparation or cold-read success.

## Exact replay after growth

`6e9804df` proves `MergedFreshOrdinaryColdReplay.collect_correct` for all
bounded outcomes with only initial cache validity. Completed records remain
available in the tables. Repaired stored substitution and unfolding replay
their exact results after growth. `collect_replay` and `nodeEdges_replay`
follow the actual ordered read and replay every completed subcall. They
return identical ordered edges and leave the larger cache unchanged.
Preparation, closed inputs, and semantic heaps are not premises.

`collect_stable` and `nodeEdges_stable` retain exact completed results and
caches at every larger traversal bound. `nodeEdges_replay_stable` combines
larger bounds and later caches. These laws require an actual completed read;
they do not supply one for a previously unfinished traversal.

## Rejected measures from actual closed construction

`0534aad8` adds `SourceColdUnfoldNewMuBoundary`. Actual repaired source
construction builds `mu x. mu y. f(x,y)` from empty caches. One actual closed
unfolding creates a new closed Mu record. Cached depth increases from 2 to 3.
The source node counter increases from 13 to 17. The returned Mu key was
absent in the original cache and is resident in the final cache.
`not_noNewMu` refutes retention of the initial Mu inventory.
`depth_increases` refutes descending cached depth as a general measure.
The exact repaired reader still completes with one edge and node counter 18.

A focused live Haskell reproduction in the Nix shell also reports depths
`(2,3)`, closed input and output, different root/result identities, and one
returned edge. File: `/tmp/mcfta-cold-measure-native.hs`. Log:
`/tmp/mcfta-cold-measure-native-20261014.log`. These are counterexamples to the
proposed measures. They are not termination counterexamples or source defects.

## Native heap propagation and exact final-cache guarded language

`9a0df4cb` proves `SourceRecursiveIntersectionOpenDepthEffects` and
`SourceRecursiveIntersectionOrdinaryWork`. Actual optional binders retain
the body/probe heap through their exact repaired compilation. All ordinary
compiler jobs add no Mu. `Bounds.open_depth_heaps` follows actual nested
native evaluation, checked memo lookups, source bodies, completion frames,
and continuations. It retains both semantic and body/probe heaps.
`NativeColdTable.cold_node_table` and `constructed_node_table` derive a finite
repaired cold table after successful first native execution. Complete caches,
closed Original inputs, and checked WordRanges retain their stated scope.
No preparation, output trace, or finite future cache is supplied.

`e70160d6` adds `MergedFreshOrdinaryGraph`. Its Mu epsilon step uses the actual
repaired stored executor. `MergedFreshOrdinaryExposureCertificate` derives a
finite complete constructor certificate for allocation-free completed reads.
`ExposureOrigins` proves that every returned edge has a repaired epsilon
origin in each later cache. `ExposureCoverage` proves the reverse inclusion.
`ExposureLanguage.actual_exact` retains complete guards and ordered children.
`SourceFreshOrdinaryColdTableLanguage.trace_table_language_final` identifies
the complete finite table with this repaired graph in its actual final cache.
`cold_table_language` supplies the finite trace and stable bounds.
The native cold-table theorems also return this exact guarded-language law.

The final-cache qualification is essential. These theorems do not equate
the final repaired graph with an initial graph that discards allocated caches,
or with independent intended Mu semantics. Next prove that source-language
transport through actual repaired substitution, fresh identities, and
canonical hits. Follow `substitutionPlan`; literal identity reconstruction
for arbitrary raw binders is refuted. Then derive physical
`ProductReadback.members` and `.rejected` and apply `product_exact`.
The earlier prepared graph uses the old executor; its preparation premise
remains valid in its stated fragment.

Current audit: 1,401 jobs and 43,344 theorem dependency checks. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-independent-guarded-compiler-20261014-audit.log`.

## Remaining language obligation

`b3008aba` defines independent guarded stored-record and lexical meanings.
It proves actual metadata support, normalization, cleanup, root-self filtering,
and full nested stored-plan compilation. Its substitution and unfolding laws
concern actual compiled plans. Actual repaired source execution and canonical
Mu-hit language preservation remain open. Read
[the guarded compiler note](notes-independent-guarded-language.md).
Prove actual execution and semantic probe-heap preservation together. Then
connect repaired final graph language to independent meaning and physical
product row/rejection laws. Do not repeat finite native tables or their exact
final-cache guarded readback.

## Validation

Lean 4.34.1 passes 1,401 aggregate jobs and 43,344 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-independent-guarded-compiler-20261014-audit.log`.
No Haskell source changed. The current PR #119 Nix and active-package
formatter checks remain valid.
