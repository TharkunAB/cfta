# Complete ordered class selection with both source memos

Current proof update: `9f6d66a6` adds current-policy stateful execution,
finite source checks, ordered descendant memo correctness, sequential active
ancestor separation, and receipts for all three gate memo tables. The complete
ordered class filter and native memo ownership still need source correspondence.
Read [the current memo note](notes-endpoint-memo-stateful.md). Older stateful
next targets and counts below retain their historical context.

Current source update: main `24a710a3`, merged at `6a02619c`, adds a
constrained-descendant check at ordinary path endpoints. The pure current
policy and actual-record finite checks are proved in `3eed507c`. The older
stateful/memo selection pipeline below retains its earlier policy. Caller-cycle
witnesses remain historical; the preserved cold Haskell fixture now completes.
Read [the current source comparison](notes-main-24a710a3.md). General caller
termination and the new descendant memo remain open.

Current update (2026-10-15 02:13 CEST): `ae6a0141`, `ac7c1eaf`, `97f987a1`,
and `a84343e3` derive the physical class sort, source prechecks, actual
array-normalization readback, and complete guarded selection. The next
requireAll target has a checked closed raw self-binder stutter and Haskell
reproduction. Read [the current note](notes-physical-class-order-entry.md).
Earlier next targets below retain their historical context.

Updated: 2026-10-15 01:52 CEST.
Proofs: `f3d27627`, `a93d1b35`, and `d0d8ac1f`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
Publish completed checkpoints on `formalize`.

## Actual ordered filter

`InternedSourceClassSelection.select` follows the local-class filter in
`Data.CFTA.Equality.Operations.reduceEqConstraints`. It checks every class
against the original child list. A blocked class is discarded, then later
classes still run. A clear class is retained in its original position.
Only the path scan inside each class stops at its first true decision.

The worker returns `done none` for missing gate fuel. Pending construction
remains a separate outcome. Neither outcome is a completed false decision.
The worker does not return a partial selected list as the complete result.

`Query` retains each occurrence's class, before cache, Boolean, and after
cache. `Trace` has one query per original occurrence. Its constructors link
the exact intermediate caches. `Trace.original` preserves the full original
order. Repeated classes remain separate occurrences. `selected` filters
these receipts without reordering or deduplicating them.

`trace_of_done` and `trace_complete` give both execution/graph directions.
`fuel_stable` preserves the complete result and final cache for every larger
fuel amount. `Trace.unique` determines all receipts and the final cache.
`Trace.selected_witness` and `Trace.selected_paths` give complete false gate
queries for all retained classes and their paths.

`InternedSourceClassSelectionComplete.complete` derives finite selection for
every ready cache and original available child list. Every returned cache
retains the semantic heaps and both growth histories. Later queries therefore
retain every original input. `eventually_exact` gives one finite bound for
the complete filter and exact readback at every larger bound.

## Actual memo composition

`SourceMemoClassSelection.Reads` extends the complete filter graph. Each class
occurrence has the existing full unfolding memo graph and concrete predicate
memo receipts. Both returned memos pass to every later class. A blocked class
does not discard the memo effects it produced.

`lift` derives every call from the existing class lift theorems. It supplies
all hit, miss, insertion, and growth facts. No whole-memo observation law is
supplied. `complete` derives finite stable filter execution and both returned
memo invariants. `execution_iff` gives both graph directions.

`source_edges` derives the initial constructor cache and both empty memo
tables from original source construction. Every original outgoing edge can
run the complete filter. `memo_independent` proves equality of every ordered
receipt, the selected classes, and the final constructor cache when the
starting memo tables differ. It does not equate final memo tables.

## Derived gate replay and pure readback

`InternedSourceGateReplay` proves a new source growth law for complete node,
child, edge, path, and class graphs. A completed query replays in every cache
that extends its final cache. Each actual unfolding then returns its exact
earlier result without changing that later cache. The proof uses the existing
stored unfolding replay theorem and the actual certified returned caches.
It includes arbitrary nested Mu, unions, and ordered sibling effects.

This is not an assumed whole-gate observation law. It does not assert that
arbitrary unrelated initial caches have equal decisions or identities.

`InternedSourceClassSelectionReadback.Trace.replay` lifts that law to every
class receipt above the complete filter's final cache. Thus every receipt can
be compared in one retained cache. `decision` is the total pure Boolean
derived from finite source class execution in a certified cache.
`decision_complete` retains its actual logical source graph.

`guarded` installs that derived read in `EqualityReduction.Operations`.
`Trace.selected_eq_guarded` proves exact ordered equality with
`EqualityReduction.selectedClasses` in the complete filter's final cache.
There is no supplied cache-independence or gate-correctness premise.

`finish` applies the existing empty/contradiction cases, required-path union,
right fold of class edits, and empty propagation to this selected list.
`Trace.pass_readback` identifies it with the existing pure pass.
`Trace.pass_exact` retains the existing one-pass constrained forest theorem
under the explicit local primitive-operation laws. This theorem does not
derive native intersection, projection, required-path, or edit contracts.
It does not prove termination of repeated fixed-point reduction.

`SourceMemoClassSelectionReadback.source_selected` derives original source
construction, both actual memo graphs, finite exact execution, and complete
pure selected-class readback together. It needs no completed construction,
successful gate call, or whole-node predicate premise.

The class input here is an ordered list. This work does not yet derive the
physical `unsafeSubsumptionOrderedEclasses` list from source constraint
payloads. It also does not claim that the source caller evaluates the filter
before its early empty and contradiction guards. Those guards must precede
selection in the physical caller proof.

The logical scalar normalization and total decision wrappers remain
noncomputable. Native memo containers, lazy scheduling, primitive resources,
external solvers, and verified Haskell extraction retain their limits.
The exact Sized contracts, optimized interned core, and unary ancestor
theorem remain. No production Haskell code or dependency changed.

## Next source adapter

Read `Data.CFTA.Equality.Constraint.unsafeSubsumptionOrderedEclasses` and
`completedSubsumptionOrdering`. Model the source `sortBy` result, including
the reverse structural fallback. Do not substitute a convenient comparator
or infer the physical order from a different sorting algorithm without proof.
Keep raw constructor payloads distinct from normalized consistent inputs.
`EqualityNormalize.fixedPoint_subsumption_transitive` and
`consistent_subsumption_irreflexive` supply the existing normalized relation
facts. They do not establish a lawful comparator for arbitrary raw inputs.

Derive the early empty and combined-contradiction branches before selection.
Show why the unsafe class accessor cannot see `EqContradiction` in the live
branch. Then connect the actual required-path and narrowing primitives to
the one-pass laws. Preserve the original child list during all gate queries.

## Validation and preservation

Pinned Lean 4.34.1 builds all six focused modules. The aggregate audit passes
1,609 jobs and checks 45,030 theorem dependencies. It permits only `propext`,
`Classical.choice`, and `Quot.sound`. Only the old unused `inputs` warning
remains. Log: `/tmp/mcfta-ordered-class-selection-20261015-audit.log`.

All older proof bytes are unchanged except six new audit imports.
All fixtures, counterexamples, repros, marked drafts, backups, stashes, and
other worktrees remain. Snapshot:
`/tmp/mcfta-ordered-class-selection-checkpoint-20261015-0152/`.
It saves 1,997 Lean-tree files and four root documents.
