# Actual stored-plan binder depth

Updated: 2026-10-14 15:49 CEST. Latest proof checkpoint: `b3008aba`.
The compiler and zero-case proof is now `c269539f` after the PR #122 rebase. Its earlier
hash `7f1daf23` remains in the preserving backup.

## Proved compiler correspondence

`InternedStoredPlanBinderDepth.valueDepth` treats a closed record as a
constant. Otherwise it counts maximum open Mu nesting through actual node
children, union members, and stored bodies. Probe metadata is not traversed.
`bodyDepth` applies that measure to the stored body of an outer Mu.
It is different from cached `Value.depth`.

`syntaxDepth` counts maximum binder nesting in source constructor syntax.
`encode_depth` proves that the actual stored compiler emits exactly
`valueDepth` binder nesting. The theorem retains arbitrary context and local
name lists. It requires no record coherence, preparation, or execution
premise. Ordered member and edge variants retain the same exact measure.

`Path.plan_depth_bound` follows actual source callback paths. The depth of
the reached expression plus the number of crossed callbacks is at most
the original source-plan depth. This is a static source-path bound.
It does not bound the size of later stored records after canonical readback.

## Proved zero case

`syntax_zero` states that source-plan depth zero is exactly `BinderFree`.
The ordered list and edge variants also hold. `execute_zero_noNewMu` derives
that repaired stored execution of a zero-depth record cannot add a Mu.
`unfold_zero_noNewMu` applies this result to actual outer unfolding when its
body-plan depth is zero. Ordinary node and edge allocations remain possible.
No preparation, validity, or semantic-heap premise is required for this
absence of new Mu records.

## Actual normalization bounds and the positive depth-one case

`262242f9` proves that coherent available records satisfy
`valueDepth value ≤ value.depth`. The actual repaired ordinary placeholder
also bounds this measure. Closed captures can make the cached bound loose.
This does not make cached depth a decreasing unfolding measure.

`1e28a69c` proves open-depth bounds through actual node construction, union
flattening and merging, canonical cache readback, and root self filtering.
`InternedStoredPlanBinderDepthFlat.callback_bound` follows binder-free
callbacks with arbitrary closed captures and bounded open lexical inputs.

`InternedStoredPlanBinderDepthOne.build_new_zero` follows every actual
source branch whose maximum binder depth is at most one. Each final Mu is
an exact earlier record or has an open body plan of depth zero. The initial
cache can contain deeper Mu records. `execute_new_zero` derives the same
property for actual stored substitution with zero-depth replacements.
`unfold_new_zero` applies it to closed available input with body depth at
most one. `unfold_one_decreases` proves strict decrease for every new Mu
when that original body depth is one. It examines the complete returned
cache, including probe allocations. No preparation, source semantic heap,
or supplied successful outcome is required. Cached capture depth is unbounded.

The depth-one checkpoint audit passed 1,375 jobs and 42,935 theorem
dependency checks. Log: `/tmp/mcfta-open-depth-one-20261014-audit.log`.
This earlier depth-one scope is superseded by the general theorem below.
Finite repeated cold traversal and physical product language remain open.

## General actual open-depth correspondence and unfolding progress

`482cc0e2` proves exact open depth through actual union reconstruction,
ordinary merging, canonical readback, and root self filtering.
`InternedOpenDepthSemantics` uses the existing free-name and empty-shape
observations plus separate lexical depth inputs. A closed binder result
has depth zero. External renaming and both actual probe arguments preserve
the interpreted depth. The static source plan plus its input depth bound
bounds this interpretation.

`InternedOpenDepthExecution.build_depth` follows every actual repaired
source branch. `closed_heap` and `closed_probe_equal` derive equal open
depth for every complete Mu body and its Depth probe from actual empty-
cache construction. This covers raw and smart binders, arbitrary closed
captures, canonical hits, and all probe records. The old cached-depth heap
and free-name observations determine the exact cleanup branch.
`build_bound` and `callback_bound` derive actual returned-value bounds.

`de322a41` proves `InternedStoredPlanBinderDepthProgress.build_new_lower`.
With zero-depth lexical inputs, every complete Mu in the returned cache
is an exact initial record or has body depth strictly below the original
plan depth. `execute_new_lower` follows the actual stored compiler.
`unfold_new_lower` and `unfold_decreases` prove general strict progress for
closed unfolding. Every newly allocated Mu is covered, including open
probe records. `constructed_unfold_decreases` derives all heap premises
from actual empty-cache construction. No preparation, supplied successful
outcome, or assumed progress law is used. `execute_heap` and `unfold_heap`
preserve the new body/probe invariant for subsequent actual source work.

The aggregate audit passes 1,381 jobs and 43,054 theorem dependency checks.
Log: `/tmp/mcfta-open-depth-progress-20261014-audit.log`.
The three permitted axioms remain `propext`, `Classical.choice`, and `Quot.sound`.
The primary Sized source results remain intact. Later checkpoints prove
general finite cold traversal and structural final tables. General guarded
row-language preservation and physical product language remain open.

## Proved positive-depth target

For actual source-derived caches, consider one completed unfolding of a
closed available Mu. Every newly allocated Mu has strictly smaller
`bodyDepth` than the unfolded Mu, by `unfold_decreases`. This includes open probe records.
`constructed_unfold_decreases` derives the cache premises from actual
source construction. Canonical hits and fresh body names are covered.
The cached-depth and raw identity-substitution counterexamples remain.

The progress theorem permits counts of unfinished closed Mu unfoldings
by decreasing body depth in the finite current cache. A completed
unfolding settles its own replay. Cache growth preserves settled calls. Any new unfinished closed
Mu would have a lower degree. A fixed maximum degree and lexicographic
degree counts replace the old fixed-inventory budget in the reader proof
below. Closed-reader invariants exclude open pending inputs. Finite final
cold tables and product language remain open.

## Exploratory evidence

`/tmp/mcfta-open-rank-probe.lean` checks the same measure recurrence on 1,336
generated closed expressions. The grammar includes empty, scoped variables,
smart and raw binders, unions, and unary and binary nodes. The list can
contain repeated expressions. For each source build it examines every
closed Mu in the complete constructed inventory, including probe records.
It unfolds each such Mu and examines every newly allocated closed Mu in
the complete returned inventory. Construction or unfolding failures and
non-decreasing new closed Mu measures would be reported.

The completed output is `1336` followed by `[]`. Log:
`/tmp/mcfta-open-rank-probe-20261014.log`.
This earlier finite search is validation only. The later general theorem
proves the positive-depth property. General termination remains open.
Do not repeat the search without a changed measure, broader grammar, or
another concrete reason.

The temporary live Haskell search `/tmp/mcfta-open-rank-native-search.hs`
checks 1,336 closed and 2,040 sentinel-capturing expressions. It examines Mu
records reachable from the final root through children, bodies, and probes.
It does not inspect unreachable discarded records in the global cache.
No examined stored body has open depth above the maximum of its two probes.
Log: `/tmp/mcfta-open-rank-native-search-20261014.log`.

The two repaired live Haskell alias/stutter cases report `(1,1,1)` and
`((1,1,1),(3,3,3),(2,2,2))` for their body and probe depths. Log:
`/tmp/mcfta-open-rank-probes-native-staged-20261014.log`.
This earlier evidence did not prove the invariant. The later actual source
induction now proves equality of body and Depth-probe open depth.
A stronger temporary Haskell check compares each stored body's open depth
with its Depth probe. It uses the same 1,336 closed and 2,040 capturing
expressions and reports no mismatch. File:
`/tmp/mcfta-open-depth-equality-search.hs`; log:
`/tmp/mcfta-open-depth-equality-search-20261014.log`.
The formal source induction now supplies the general equality proof.

The corresponding larger staged Lean evaluation exceeded its ten-minute cap and was stopped with exit 130 and no result. It is inconclusive. File:
`/tmp/mcfta-open-rank-probes-bound.lean`. Do not repeat it without a changed
strategy. No proof or runtime failure follows from this interrupted probe.

## Proved dynamic reader budget

`6132e4f2` adds `InternedMuDepthInventory`. Its finite counts include each
complete Mu only at its canonical issued identity. This avoids duplicate
reservations for one key. Initial cached depth supplies a maximum body
degree. Future cached depth need not decrease. The count comparison uses a
common finite range and does not assume that `Grows` includes issued counters.

`MergedFreshOrdinaryColdTermination.collect_complete` derives a successful
bound for every available closed worklist in a complete semantic cache with
the proved body/probe heap. The fixed finite vector counts unseen canonical
Mu identities by decreasing body depth. Structural pending work has lowest
priority. Actual unseen unfolding consumes its degree and adds Mu only at
lower degrees. The proof permits all probe allocations and retains the heap
for subsequent reads. It assumes no preparation, `NoNewMu`, successful trace,
finite future cache, or external progress law.

`nodeEdges_complete` covers both public reader paths. `read_closed` also
retains semantic heaps, coverage, exact growth/history, resident closed
edges, and identical edges and cache at every larger read bound.
`constructed_read_closed` derives all cache premises from actual repaired
empty-cache source construction.

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

## Validation

Lean 4.34.1 passes 1,401 aggregate jobs and 43,344 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-independent-guarded-compiler-20261014-audit.log`.
No Haskell source changed. Existing Nix and active-package formatter checks
remain valid.
