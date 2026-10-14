# Actual stored-plan binder depth

Updated: 2026-10-14 14:05 CEST. Latest proof checkpoint: `1e28a69c`.
The compiler and zero-case proof is now `d0680cbe` after rebase. Its earlier
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

The aggregate audit passes 1,375 jobs and 42,935 theorem dependency checks.
Log: `/tmp/mcfta-open-depth-one-20261014-audit.log`.
The next positive-depth target is depth two and above. General finite cold
traversal and physical product language remain open.

## Proposed positive-depth target

For actual source-derived caches, consider one completed unfolding of a
closed available Mu. The proposed next property is that every newly
allocated closed Mu has strictly smaller `bodyDepth` than the unfolded Mu.
The property is proved when the original body depth is one.
Depth two and above remain unproved. Do not use it as a theorem or a supplied contract.
Canonical hits and actual fresh interned body names must be handled.
The cached-depth and raw identity-substitution counterexamples remain.

If the property holds, count unfinished closed Mu unfoldings by decreasing
body depth in the finite current cache. A completed unfolding settles its
own replay. Cache growth preserves settled calls. Any new unfinished closed
Mu would have a lower degree. A fixed maximum degree and lexicographic
degree counts could replace the old fixed-inventory budget. No such dynamic
budget has been implemented. Closed-reader invariants already exclude open
pending inputs. Finite final cold tables and product language remain open.

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
This finite search is validation only. It does not prove the proposed
positive-depth property or general termination. Do not repeat the search
without a changed measure, broader grammar, or another concrete reason.

The temporary live Haskell search `/tmp/mcfta-open-rank-native-search.hs`
checks 1,336 closed and 2,040 sentinel-capturing expressions. It examines Mu
records reachable from the final root through children, bodies, and probes.
It does not inspect unreachable discarded records in the global cache.
No examined stored body has open depth above the maximum of its two probes.
Log: `/tmp/mcfta-open-rank-native-search-20261014.log`.

The two repaired live Haskell alias/stutter cases report `(1,1,1)` and
`((1,1,1),(3,3,3),(2,2,2))` for their body and probe depths. Log:
`/tmp/mcfta-open-rank-probes-native-staged-20261014.log`.
This supports a candidate probe-bound invariant but does not prove it.
The corresponding larger staged Lean evaluation exceeded its ten-minute cap and was stopped with exit 130 and no result. It is inconclusive. File:
`/tmp/mcfta-open-rank-probes-bound.lean`. Do not repeat it without a changed
strategy. No proof or runtime failure follows from this interrupted probe.

## Validation

Lean 4.34.1 passes 1,375 aggregate jobs and 42,935 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-open-depth-one-20261014-audit.log`.
No Haskell source changed. Existing Nix and active-package formatter checks
remain valid.
