# Actual stored-plan binder depth

Updated: 2026-10-14 13:30 CEST. Proof checkpoint: `7f1daf23`.

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

## Proposed positive-depth target

For actual source-derived caches, consider one completed unfolding of a
closed available Mu. The proposed next property is that every newly
allocated closed Mu has strictly smaller `bodyDepth` than the unfolded Mu.
This property is unproved. Do not use it as a theorem or a supplied contract.
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

## Validation

Lean 4.34.1 passes 1,371 aggregate jobs and 42,877 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-stored-plan-depth-20261014-audit.log`.
No Haskell source changed. Existing Nix and active-package formatter checks
remain valid.
