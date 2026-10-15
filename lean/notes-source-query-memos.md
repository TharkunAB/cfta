# Actual query unfolding receipts and ordered class entry

Proof checkpoint `60a8d3eb`, source main `525d722e`. The starting checkpoint
is `11fb07a1`. Full library scope stays active. All older constructor and
equality proofs and the optimized interned core remain.

## Actual global unfolding calls

`SourceQueryUnfoldMemo.run_of_unfold` starts with actual completed stored
unfolding and current semantic/cost readiness, availability, and memo
coherence. It derives the identical memo-call output and constructor heap,
returned coherence, and retention of every earlier entry. A miss inserts
only at an absent key. A hit leaves the table unchanged. valid_grows retains
coherence of all three gate tables through actual constructor Keeps.
This growth result does not assert that no new memo calls occur.

`SourceEqualityExposureMemos.CollectReads` records each demanded Mu call in
the bounded source worklist. Visited values skip the call. Empty, ordinary,
reference, union, exhausted, and completed cases retain their exact source
behavior. NodeEdgesReads retains the first Mu call. If its result is not
ordinary, collection restarts on the original Mu in the returned heap and
memo. The subsequent call can hit the result saved by the first.
collect_reads/nodeEdges_reads derive final coherence and retained entries.
They do not need closed inputs or a supplied final memo invariant.

`SourceEqualityProjectionMemos` follows actual Read, Head, ReadAll, Union,
Project, ProjectRows, and Forest graphs. It records every exposure call in
source order. Node reconstruction changes no unfolding table. Selected
children pass the exact returned table to later rows. Current semantic/cost
effects derive all intermediate premises. forest_reads derives coherent
final unfolding records and preserves every earlier completed entry.

`SourceEqualityQueryGlobalMemos` adapts exposure, forest projection, and
scoped Operand receipts to all three gate tables. Both query tables remain
unchanged in these operations. Their final coherence follows from the
actual constructor growth and issued history. The unfolding table follows
the new actual call receipts. No future-validity premise is supplied.
The scoped native domain and node/edge memo state remains distinct.

These are effects of supplied completed projection graphs. They do not
derive those graphs for every open input. Operations.union also has a
deferred open-operand branch. That branch is not added here. The existing
supported class-query proof derives closed projected operands separately.

## Ordered normalized class entry

`SourceEqualityLazyClassEntry.ordered_entry` starts from original physical
Record values, their Coherent facts, Cached stored equalities, and exact
sourceEqualities accessor readback. It derives coherence and Active for the
exact ClassOrder.ordered result, plus satisfaction equivalence with the
original accessor. live_entry uses the actual successful Precheck result
to identify that exact ordered output. stopped_refutes then discharges the
Scan activity premise and refutes the original accessor constraint.

Coherent original records and accessor readback remain explicit. Cached
path classes alone do not supply native PathEClass trie payloads. There is
no new theorem that extracts those Haskell records from a guard.

## Source review and next composition

The read-only source review is preserved at
`/tmp/mcfta-query-memo-native-source-review-20261015.md`.
getPath recursive heads and Operations.union call nodeEdges. Admitted
provablyEmpty rows also call nodeEdges. Its class requirements use foldr1;
the refused-class Seeded query instead uses foldr intersect with its seed.

On completed resident operands, intersectOpen enters stored Mu bodies,
resolves Rec through idFree, uses Type.createUnion, and constructs optional
binders with a fixed substFree callback. These paths and fixed constructors
do not call global unfoldOuterRec. See
`cfta/src/Data/CFTA/Interned/Operations.hs:477-519` and the review.

No existing Code-to-global-event transfer proves an empty unfolding event
trace for these native instructions. The source machine lacks the global
memo. Result equality with its kernel does not prove unchanged GHC memo
state. Instrument actual source instructions and fixed constructor callbacks,
then prove their native event behavior for completed resident inputs. Do not
replace this obligation with a predicate defined to mean unchanged memos.

Haskell native key and constructor demand can force delayed producer thunks.
Those producers can run projection or exposure. Their forcing origin and
exact demand remain outside the completed resident Lean representation.
Keep progressive row-spine demand and original child forcing explicit.
Substitution-plan and per-binder memos are additional distinct families.

Next compose actual query memo receipts through Fold/Seeded, delayed
Force/Expose/Run/Decision, and the reached Scan. Preserve all three global
gate tables. Connect concrete native class-record extraction and initial
caller construction, then compose the selected fallback. WordRanges,
completed scoped execution/exploration, newer checked allocation transfer,
general completion, waiting counts, template exclusion, broader APIs/runtime,
and all separate Sized contracts remain open.

## Validation and preservation

The pinned full audit passes 2,065 jobs and 52,088 theorem dependency checks.
Only propext, Classical.choice, and Quot.sound occur. No new warning occurs.
Log: `/tmp/mcfta-query-memo-audit-20261015.log`.
Five new modules and two additive Audit imports contain the proof change.
Older proof definitions and all four Haskell package trees are unchanged.
Their unchanged Haskell checks were not repeated.

Start: `/tmp/mcfta-lazy-prefix-checkpoint-20261015-2030/` (2,730 files).
Closing: `/tmp/mcfta-query-memo-checkpoint-20261015-2043/` (2,736 files).
Script: `/tmp/mcfta-preserve-query-memo-20261015.py`.
All prior proofs, counterexamples, repairs, marked drafts, stashes, and
other worktrees remain. New logs, probes, frozen sources, and the source
review remain in the closing snapshot. Weekly allowance is 85%.
Stop owned work at 1% or less. No board posts or deployments.
