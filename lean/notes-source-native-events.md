# Native constructor instructions and global unfolding events

Proof checkpoint `97c525f4`, source main `525d722e`. The starting checkpoint
is `1a8d5db0`. Full library scope stays active. The optimized interned core,
older constructor and equality proofs, and all separate Sized contracts remain.

## Actual primitive execution

`SourceGlobalUnfold` defines typed edge/node requests, Mu lookup, identity
reservation, first-record publication, and a global unfolding action.
`perform` executes each actual operation. The global action executes
`InternedFreshOrdinaryUnfoldMemo.run`. Its event records a call on both
hits and misses, and also on pending outcomes.

`Runs` composes actual primitive steps with exact constructor heaps.
`NoGlobal` checks the emitted events. `Runs.noGlobal` derives retention of
the unfolding table from these two facts. Table retention is not an input
to that theorem. A memo hit still has a global event, so a table-preserving
hit does not satisfy `NoGlobal`.

## Constructors and fixed callbacks

`SourceConstructorGlobalUnfold.work` independently executes each original
Work edge/node request and continuation. `work_erase` gives the exact old
result and heap. `work_runs` derives its actual primitive trace, and
`work_silent` derives absence of global unfolding actions.

The request executor retains the source lookup hit and pending branches.
A miss reserves the canonical identity before the body callback. A
completed callback publishes with keepFirst. A pending callback retains
its actual prefix and omits publication.

`SourceConstructorGlobalUnfoldBuild` expands the repaired fresh expression,
child, and edge schedules. Both binder probes execute before lookup. The
fixed native callback expands the actual stored-substitution execute
definition and withoutSelfReference work. It does not use an abstract
callback result or a supplied callback-silence premise.

`maybeMu_erase`, `maybeMu_runs`, and `maybeMu_silent` hold for complete
stored model values at every current constructor heap. They need no
Facts, Available, final-validity, or successful-completion premise.
Pending constructor outcomes remain pending.

## Native instruction transfer

`SourceNativeGlobalUnfold.step` expands the actual work and optionalBinder
instructions. It retains every other original control branch, native
lookup/demand operation, and completion frame. `step_erase` gives the
identical original native observation.

The instrumented execute uses the original native instruction bound.
`execute_erase` retains exact yielded continuations, successful values,
failures, blocked reasons, constructor heaps, and both native memo tables.
`execute_runs` derives the actual physical primitive trace.
`execute_silent` derives absence of global unfolding actions.
`execute_receipt` attaches these derived facts to the original executor.
These theorems include all bounded outcomes. They do not establish that
every native request eventually succeeds.

`SourceNativeGlobalMemos.scoped_receipt` applies the transfer to an actual
completed scoped request. `scoped_memos` uses its actual semantic heap
effects to derive coherence of the same three global gate tables in the
returned heap. Initial readiness, available closed operands, and guard
conjunction semantics remain explicit for this coherence result.
The operational event receipt itself needs none of those premises.

## Source and runtime boundaries

Native intersectOpen enters stored Mu bodies and uses Type.createUnion.
Its optional binder uses the fixed substFree callback. These instructions
make no direct unfoldOuterRec call on completed resident operands. See
`cfta/src/Data/CFTA/Interned/Operations.hs:477-519` and
`cfta/src/Data/CFTA/Interned/Type.hs:733-753,809-817,876-900`.

The global primitive tracks the unfolding table. The three-table adapter
derives same-table coherence. It does not establish predicate/descendant
helper-call silence. The source unfoldOuterRec is Mu-only. Existing
exposure adapters retain that call shape; the generic primitive uses the
existing total unfolding-memo model.

The input model has complete resident records and pure identification
functions. Haskell identity, key, and constructor demand can force delayed
producer computations that perform projection or exposure. Exact producer
demand, row-spine sharing, original child forcing, global publication, and
concurrent ownership remain open. Substitution-plan and per-binder memos
remain distinct from the three gate tables.

## Next composition

Compose projection and native receipts through actual Fold/Seeded, delayed
Force/Expose/Run/Decision, and the reached Scan. Use the existing anchored
support results. Do not require the entire original forest to be closed.
Retain each returned global table and its coherence at the next actual
operation. Then connect concrete class-record extraction and initial
caller construction, and compose selected requireAll, class reduction,
and empty propagation.

Checked native state, machine bounds, general completion, waiting counts,
template exclusion, broader APIs/runtime, and all separate Sized contracts
remain open. The source review is in
`/tmp/mcfta-native-events-review-20261015.md`.

## Validation and preservation

The pinned full audit passes 2,070 jobs and 52,331 theorem dependency checks.
Only propext, Classical.choice, and Quot.sound occur. No new warning occurs.
The old ClosedCompletion unused-input warning remains.
Log: `/tmp/mcfta-native-events-audit-20261015.log`.
Positive global-action probes include hit, miss, pending, and visible-call
laws. All five new modules are included by one additive Audit import.
All prior proof definitions and all four Haskell package trees are unchanged.
Unchanged Haskell checks were not repeated.

Start: `/tmp/mcfta-query-memo-checkpoint-20261015-2043/` (2,736 files).
Closing: `/tmp/mcfta-native-events-checkpoint-20261015-2105/` (2,742 files).
Script: `/tmp/mcfta-preserve-native-events-20261015.py`.
All prior proofs, counterexamples, repairs, marked drafts, stashes, and other
worktrees remain. Weekly allowance is 85%. Stop owned work at 1% or less.
No board posts or deployments. Push verified formalize checkpoints.
