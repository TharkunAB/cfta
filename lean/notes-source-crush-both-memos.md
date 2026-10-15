# Exact visited source checks and both gate memos

Current update (2026-10-15 02:13 CEST): `ae6a0141`, `ac7c1eaf`, `97f987a1`,
and `a84343e3` derive the physical class sort, source prechecks, actual
array-normalization readback, and complete guarded selection. The next
requireAll target has a checked closed raw self-binder stutter and Haskell
reproduction. Read [the current note](notes-physical-class-order-entry.md).
Earlier next targets below retain their historical context.

Current update (2026-10-15 01:52 CEST): `f3d27627`, `a93d1b35`, and `d0d8ac1f`
complete the ordered class filter with both memo tables. Each class occurrence
retains its exact intermediate caches. Derived gate replay connects all
decisions to the pure selected-class operation in the retained final cache.
Read [the current note](notes-ordered-class-selection.md). Earlier next
targets below retain their historical context.

Updated: 2026-10-15 01:40 CEST.
Proofs: `0f5f465f`, `348e5adc`, and `9abb1aff`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
Publish completed checkpoints on `formalize`.

## Exact visited fold

`InternedSourceCrushSemantics.sourceChildren` reads ordinary edge children,
stored Mu bodies, and union members. Empty records and bare references have
no children. Neither Mu probe participates. `Reaches` is the independent
physical descendant relation. It does not unfold bare references.

`Summary` records four properties of an actual visited traversal. Every root
entry is visited. Newly visited entries are closed under source children.
Every new entry comes from a reached record. The Boolean is true exactly
when every newly visited available record passes its local edge checks.
Sequential composition uses the actual returned visited list of each child.

`InternedSourceCrushSummary` derives this summary for each actual worker by
mutual structural induction. On a repeated identity, canonical coherence
identifies the complete immutable record. `Added.drop_head` therefore joins
the local root check with its actual child checks. No assumption states
correctness of the whole fold. Unrelated cached edges need not pass `plain`.

`InternedSourceCrushCorrect` derives final visited coverage from root entry
and closure. `unconstrained_exact` proves both directions: the concrete fold
is true exactly when every physically reached ordinary edge passes `plain`.
`unconstrained_false` supplies an actual reached failing edge. Both results
include repeated canonical identities, arbitrary open nested Mu, and root
unions. The existing finite distinct visited-inventory bound remains.
It is separate from a machine runtime bound.

`SourceMemoGateSemantics` applies both laws to the concrete source constraint
test. `plain_accepts` connects that test to the existing guard meaning.
`reached_accepts` derives the same always-accepting constraint for every
physically reached edge under normalized source annotations. It uses actual
edge residency and the constraint heap. No global plain-cache premise occurs.
A failed plain test is not a proof that its guard rejects every term.

## Both actual memo tables

`SourcePredicateGateTrace` extends the existing complete unfolding graph.
`NodeReads`, `ChildReads`, and `EdgesReads` take that graph as an index.
They add an actual `SourceUnconstrainedMemo.run` equation at each Mu query.
Blocked and closed queries retain the returned predicate memo. Open queries
pass that memo through the actual unfolding and recursive gate call.
Non-Mu dispatch adds no predicate call.

`Keeps` retains the existing complete constructor invariant, unfolding memo
coherence, both growth histories, and predicate memo coherence. The two memo
tables remain separate. `SourcePredicateGateLift.lift_node` derives each
predicate receipt from `run_exact`. It reuses `run_complete` to certify the
already recorded unfolding result. Actual constructor growth preserves every
earlier predicate entry. False child queries pass all three returned tables
to the next edge. True queries stop before the suffix.

`SourcePredicateGateClasses` adds path and complete class receipts. Its
`lift_class` uses each actual intermediate constructor cache and both memo
tables. `complete_node` and `complete_class` derive finite source execution
and exact final constructor caches. Every larger gate fuel amount gives the
same result. The memos use logical call graphs with actual runner equations;
no separate extracted memo backend is introduced.

`source_nodes` and `source_classes` derive the initial constructor cache and
both empty memo invariants from original source construction. No completed
construction, successful gate call, whole-node predicate, or whole-memo
observation law is supplied. `class_trace_iff` gives both graph directions.
`memo_independent` retains the class decision and final constructor cache
when starting memo tables differ. It does not equate final memo tables.

The scalar guard normalization wrapper remains noncomputable in the existing
logical source model. This work does not prove native memo container,
lazy Haskell scheduling, primitive resource, external solver, or extraction
correspondence. Exact Sized reference, optimized, and solver-decided contracts
remain. The optimized interned core remains. No Haskell dependency changed.

## Next caller

Carry both memo tables through the complete ordered local-class filter in
`Data.CFTA.Equality.Operations.reduceEqConstraints`. Every class reads the
original child list. A blocked class does not stop later classes. A true
path only stops that class's internal `any` scan. Preserve the exact retained
class order, repeated class occurrences, intermediate caches, and both memo
tables. Derive finite completion and per-occurrence complete gate receipts.

Then connect the result to `EqualityReduction.selectedClasses`. Its pure
`blocked` field must have a proved readback law. If the law compares queries
in different constructor caches, derive the required growth invariance.
Do not infer it from fixed-initial-cache memo independence. Keep missing
fuel separate from a completed source decision. Reuse the completed rank,
fold, and memo composition proofs.

## Validation and preservation

The pinned Lean 4.34.1 aggregate audit passes 1,603 jobs and checks 44,981
theorem dependencies. Only `propext`, `Classical.choice`, and `Quot.sound`
occur. Only the old unused `inputs` warning remains. Focused builds pass for
all seven new modules. Audit log:
`/tmp/mcfta-source-crush-both-memos-20261015-audit.log`.

All older proof bytes are unchanged except seven new audit imports.
Counterexamples, repros, marked drafts, backups, stashes, and other worktrees
remain. The preservation snapshot is
`/tmp/mcfta-source-crush-both-memos-checkpoint-20261015-0140/`.
It saves 1,990 Lean-tree files and four root documents.
