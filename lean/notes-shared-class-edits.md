# Shared target closures through simultaneous class edits

Updated: 2026-10-15 06:11 CEST.
Proofs: `c0aa73c6`, `cf98225d`, and `cb8b675a`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
The retained traversal repair is `61f2c939`. Continue on `formalize`.

## Shared state and concrete receipts

SourceEqualitySharedTargetState.State retains the actual native state and
natural-path slots for returned target values. It stores no supplied target
language. An initial state has no returned slots. A Receipt retains a literal
SourceEqualityDemandTarget.Target graph from the captured original forest,
its actual idle native entry, available inputs, original class membership,
and constructor history into the present heap.

Ready retains current native validity, idle warm tables, semantic heap,
captured original forest scope, and a Receipt for each returned slot.
Constructor-only heap advances retain all domain and native memo tables.
Literal target construction derives its stored receipt. Later heap growth
retains every older receipt and closed physical target availability.

SourceEqualitySharedTargetForce.Force has two branches. A hit returns the
stored physical value and the identical entire shared state. A miss requires
an empty slot, runs the actual demanded target graph, and stores its returned
value at the actual returned native state. ForceRanges checks target words
only for a miss. Local captured operand progress and native target completion
derive every force from these actual-prefix checks.

SourceEqualitySharedTargetLeaf.Leaf forces the target before its actual native
intersection request. Effects derive full scope and native invariants.
Independent language inclusion derives narrowing. Concrete target receipts
retain each selected original subterm when the original class is satisfied.
SourceEqualitySharedTargetLeafComplete derives finite leaves from local force
checks and actual native request checks after the returned force prefix.

## Actual simultaneous traversal

SourceEqualitySharedEditGraph retains source leaf priority, ignored list-root
callbacks, signed child selection, every original row, full guards, literal
edge/node constructors, and actual recursive Head normalization.

SourceEqualitySharedEditEffects derives Ready and every output invariant
through the common nine-case mutual graph recursor. Allowed checks that each
leaf token is an original class path. Target scope is derived at first force.
No list of eagerly available targets is required.

SourceEqualitySharedEditRetention proves exact returned-slot retention without
semantic premises. First force preserves older slots. Native requests, head
normalization, child scans, and row constructors retain them verbatim. A force
of an already returned slot must use its hit branch. It cannot reconstruct or
replace that target. This is the graph-level once-only construction property.

SourceEqualitySharedEditRanges checks target words at first force and native
leaf words after the actual force result. Later child and row plans use only
actual completed graph prefixes. SourceEqualitySharedEditComplete combines
these plans with local force/leaf progress, complete general heads, and finite
ordered control. No whole-target or whole-edit completion law is supplied.

## Executable workers and finite bounds

SourceEqualitySharedTargetWorker implements hit, miss, storage, and the
following native request. Its incomplete observations retain the shared slots
and actual native stage observations. SourceEqualitySharedTargetWorkerProofs
proves checked successful function-to-graph agreement and stable execution at
all larger projection, head, comparison, and native bound quadruples.

SourceEqualitySharedEditWorker adds an independent edit recursion bound. It
retains every actual branch, constructor heap, native table, and target slot.
SourceEqualitySharedEditWorkerSound proves checked successful execution gives
the exact graph. SourceEqualitySharedEditWorkerComplete derives five finite
bounds from every complete graph. All larger bound tuples return the identical
value and full shared state. SourceEqualitySharedEditAPI proves both execution
directions, uniqueness, and finite stable node/list execution from local checks.
Incomplete observations do not provide enclosing worker resumption.

## Independent language and original class paths

SourceEqualitySharedEditLanguage proves two bounds through all source branches.
Every output term belonged to its input. Every accepted term survives when each
callback token selects its current subterm in the original captured root and
that original root satisfies the class. Actual first-force construction derives
the leaf case. Original source constructor/head language derives every other
case. The proof supplies no global LeafLaw.

SourceEqualitySharedClassEdits compiles the actual signed right-fold edits with
the original natural class path as each leaf token. Coherent nontrivial classes
derive supported disjoint nonroot paths. The independent compiler condition is
then the original path's actual readback. The class-level theorem proves output
inclusion and preservation of every accepted original class-satisfying term.
Under ClassSat, output and input forest acceptance are equivalent. This is a
no-loss result; it does not claim that a single class edit enforces equality.

Its complete theorem derives finite stable compiled class execution and every
returned invariant from the captured closed forest, Ready, and actual-prefix
range checks. Initial_ready supplies Ready for unforced slots at the actual
native entry. Later classes must get new class-local slots and capture their
own current forest while retaining that same native state.

## Kernel checks and validation

SourceEqualitySharedEditExamples uses a coherent active physical class with
paths [0,0] and [1,0]. Each original forest node has two distinct rows. Four
physical leaves share two target slots. Actual projection and general merge
construct the targets. Native intersections retain one warm node memo cell.
A repeated batch needs zero projection, head-read, and comparison bounds and
returns identical native state and target slots. Both slots return at zero
bounds for all target stages. Missing signed positions and list-root callbacks
force no target. Evaluation uses kernel cbv, without native evaluation axioms.

All eighteen new modules pass focused builds. The aggregate audit passes
1,745 jobs and 47,143 theorem dependency checks. Only propext, Classical.choice,
and Quot.sound occur. Only the older unused inputs warning remains.
Log: /tmp/mcfta-shared-class-edits-20261015-audit.log.
Snapshot: /tmp/mcfta-shared-class-checkpoint-20261015-0611/.
It retains 2,148 Lean-tree files and four root documents. All older proof bytes
except audit imports, all counterexamples, marked drafts, production source,
stashes, and other worktrees are preserved. The 645 earlier Haskell examples
and formatter checks apply to the unchanged source and were not rerun.

## Next source composition

Compose the actual selected class list in its source ordered right fold. Each
class captures the forest returned by later classes and starts its own unforced
slots. Retain actual full native state between classes. Model the literal
structural empty propagation once after the complete fold. Derive prefix range plans,
finite stable execution, and no loss of class-satisfying terms. Compose these
results with the existing selected/required-path graph before the whole one-pass
source worker. Keep full one-pass correspondence, open contexts, repeated fixed
points, getAllAtPath, native containers, GHC lazy scheduling, and extraction
explicit. No target slot proof establishes verified GHC heap extraction.
