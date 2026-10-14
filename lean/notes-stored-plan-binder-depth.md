# Actual stored-plan binder depth

Updated: 2026-10-14 14:34 CEST. Latest proof checkpoint: `de322a41`.
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
The primary Sized source results remain intact. General finite repeated
cold traversal, final tables, and physical product language remain open.

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

## Next dynamic budget

First prove finite execution of the actual repaired cold collector. Use a
fixed maximum body depth from the finite initial `nodeInventory`. Count
unseen Mu identities at each degree in decreasing order. Include open
probe records in this inventory. Append the existing structural pending-
work measure after those counts. Each unseen queried Mu is closed by the
proved reader invariant. Its actual unfolding consumes that degree and can
add Mu only at lower degrees. Union visits do not increase the counts.

Derive the vector change from actual coherent inventory membership and
issued identities. Do not assume a finite future cache. A nested product of
natural orders can prove well-foundedness for the fixed vector length.
Connect that measure to the actual transition before claiming termination.
Existing source completion and bounded closed-reader effects supply the
non-rank premises. The new open-depth heap is retained by actual unfolding.

Then derive finite shared traversal and its exact final tables. Row reads
reset the local seen list. Use the existing allocation-free replay of
completed unfolds to avoid charging the same Mu repeatedly. Also transfer
the new heap through actual native execution before claiming that scope.
The native successful result and semantic heap proofs remain intact, but
their older semantic-heap predicate does not include the new open-depth heap.

## Validation

Lean 4.34.1 passes 1,381 aggregate jobs and 43,054 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-open-depth-progress-20261014-audit.log`.
No Haskell source changed. Existing Nix and active-package formatter checks
remain valid.
