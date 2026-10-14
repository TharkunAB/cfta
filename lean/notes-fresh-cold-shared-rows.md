# Repaired cold shared traversal and exact Sized classes

Updated: 2026-10-14 15:49 CEST. Latest table checkpoint: `b3008aba`.
General shared termination: `68e790f0`.
Earlier checkpoints: `c410bc0a` and `75c50b4d`.

## Direct repaired executor

`SourceFreshOrdinaryColdSharedRows.collect` follows the native shared
worklist. It skips empty values and already stored identities. A first read
calls `MergedFreshOrdinaryExposure.nodeEdges`. The worklist stores the exact
returned ordered edges before it follows their children. Every next step
uses the actual cache returned by that read. Reader failures remain distinct.

`Trace` retains each actual read bound, ordered row list, intermediate cache,
and first insertion. `Trace.finite` derives finite worklist and uniform read
bounds for each finite trace. Every larger pair of bounds has the identical
result table and final cache. `collect_trace` recovers that exact trace from
any actual successful bounded run. No correspondence contract is supplied.

## General trace effects

`Trace.correct` follows actual repaired reads. Initial complete semantic
heaps, coverage, available closed work, and resident earlier rows suffice.
The exact final cache retains complete semantic heaps and coverage. Physical
growth and issued history preserve all earlier records. First insertions
extend the row map. Every final row retains an available closed root,
resident edge payloads, and closed children. Preparation and `NoNewMu` are
not premises. This theorem applies to a finite actual trace; it does not
derive general finite trace existence.

## Exact prepared bridge

`of_prepared` transfers the earlier finite prepared trace to the repaired
executor. `Trace.to_prepared` proves the reverse direction. Each induction
uses the derived prepared reader equality at the actual intermediate cache.
It also derives the preparation needed by the next step. Values, rows,
constraints, traversal order, identities, and final caches are identical.
The proof does not assume allocation-order equality outside this fragment.

`cold_finite` derives an actual repaired finite trace and stable executable
bounds for every prepared closed available root. It uses the existing
source-derived finite Mu inventory in precisely that prepared scope.
Existing exact table-language, native Sized, and solver-decided Sized
compositions therefore retain the identical physical table through the
derived trace bridge. Their validation and external solver contracts remain.

## Actual first-order Sized composition

`SourceFirstOrderFreshColdSized.source_sized` starts with arbitrary finite
binder-free body syntax and either source binder form. Actual repaired
empty-cache construction supplies the closed prepared result. Actual repaired
cold shared traversal completes without warmup or a supplied trace.
Its exact table supplies these laws:

- Each size class contains exactly the original guarded accepted terms of
  that node count. Each term occurs once.
- Each size class has a finite reference evaluation.
- Bounded prefixes are distinct, complete through the bound, and ordered by
  nondecreasing node count.
- Distinct-term rank and unrank satisfy both inverse laws.

The primary finite-key public native and solver-decided Sized contracts
remain unchanged. This result makes the repaired shared executor explicit
in the first-order construction path.

## General finite shared traversal

`68e790f0` adds `InternedFreshMuUnfoldBudget`. Counts use actual unfinished
canonical Mu records by body degree. Completed unfoldings are settled, and
actual allocation-free replay preserves settled calls after cache growth.
`unfold_progress` gives strict finite-vector decrease or exact cache equality.
`MergedFreshOrdinaryColdBudget` retains that result, the body/probe heap,
and the maximum degree through every completed actual closed read.

`SourceFreshOrdinaryColdSharedTermination.complete` follows the actual shared
worklist. A changing cache reduces the unfinished-degree vector. An unchanged
cache lets the new row consume an unvisited issued identity. Empty and known
values reduce pending length. `cold_finite` derives an actual finite trace
and uniform stable outer/read bounds. `constructed_cold_finite` derives all
heap premises from actual repaired empty-cache source construction.
No preparation, `NoNewMu`, finite future inventory, or supplied trace is
assumed. General finite final-map readback and row-language preservation are
next. Native body/probe heap propagation and physical product language remain
separate obligations.

## Finite general final tables

`3dc8f856` adds `SourceFreshOrdinaryColdTable`. Every first-written row is
retained. `Trace.closed` declares every nonempty child in the final map.
`Trace.replayed` gives an available closed root and an identical allocation-
free final-cache read for every stored row. `keys_exact` uses the actual final
issued counter and proves a finite distinct exact map domain. `keys_ascending`
proves the native ascending identity order. `cold_table` combines these facts
with the actual finite trace, stable outer/read bounds, semantic heaps,
coverage, the body/probe heap, growth/history, and resident closed edges.
No preparation, fixed future cache, or supplied trace is assumed.

The aggregate audit passes 1,401 jobs and 43,344 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-independent-guarded-compiler-20261014-audit.log`.
This earlier result proves finite table structure and exact row readback.
The later native and repaired-language checkpoints below also prove native
heap propagation and final-cache guarded row language. Initial-source
language transport and physical product language remain open. The earlier prepared graph uses the old stored
executor. Do not remove its preparation premise from termination alone.

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

## Raw-binder reconstruction boundary

`75c50b4d` adds `InternedStoredRawIdentityBoundary`. Actual repaired closed
construction builds `mu x. rawMu unused. f(x)`. Its open stored body contains
an unused raw Mu. Substitution replaces the outer reference with itself.
The exact resulting body has a different identity and cached depth 0 instead
of 1. Free-name lists remain equal. Kernel evaluation proves this observation.

The earlier `substFree` comment stated an unqualified physical identity
postcondition. That claim fails for this raw-binder case. Upstream PR #121
now limits the comment to binders made by `createMu`. The qualified law
remains unproved in the source model. `substitutionPlan`
rebuilds an open Mu body with smart `createMu`, which removes the unused
binder. It intentionally avoids pattern-synonym matcher fast paths.
A general reconstruction proof must model that cleanup. No language change
is claimed. Runtime behavior was not changed.

The live Haskell reproduction uses `createMu` outside and
`createMuDontCleanup` inside. It substitutes the outer `RecInt` with itself
in the stored body. The observation is `(False,1,0)` for equality and the two
nested-Mu counts. File: `/tmp/mcfta-identity-substitution-native.hs`. Log:
`/tmp/mcfta-identity-substitution-native-20261014.log`.

## Validation

Lean 4.34.1 passes 1,368 aggregate jobs and 42,779 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-raw-identity-20261014-audit.log`.
No Haskell source changed. The current upstream Nix suite and active-package
formatter checks remain valid.
