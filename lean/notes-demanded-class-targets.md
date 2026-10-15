# Demanded targets for original physical equality classes

Updated: 2026-10-15 05:46 CEST.
Proofs: `e38dc119`, `388f111b`, and `92d59cfd`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
The retained traversal repair is `61f2c939`. Continue on `formalize`.

## Actual operand demand

SourceEqualityNativeMerge wraps actual general merge execution in an existing
full native state. The constructor heap changes at its literal returned heap.
The domain and both native memo tables remain at their actual values. General
completion and independent-language inclusion lift through this wrapper.

SourceEqualityTargetOperand.Operand first runs actual forest getPath. It then
runs general merge at the projection's actual returned heap. Effects derive
idle native validity, semantic heaps, both cache histories, and closed
available outputs. Captured original forests remain available through their
real earlier base. Every demanded operand completes locally. Proper signed
paths retain each selected subterm of an accepted original forest.

## Source first-seeded demand graph

SourceEqualityDemandTarget defines Fold and Target. The source empty target
returns EmptyNode. A nonempty target takes its first path as seed and folds
the remaining paths from right to left. Each recursive stage demands its left
operand before the tail. The base demands the seed. The native request then
uses the exact state returned by the tail. This models strict operand demand
before native memo request publication. It does not prepare all operands
before the first native step.

SourceEqualityDemandTargetLanguage proves that each common selected original
subterm survives this target. Actual projection and merge inclusion supply
operand coverage. Each actual native Step supplies intersection language.
All earlier captured forest values retain scope through literal cache histories.
The target is an over-approximation of the common original subterms. It is not
claimed to enforce equality by itself or to have exact projected language.

## Finite checked execution

SourceEqualityDemandTargetComplete gives FoldRanges and TargetRanges. Native
WordRanges refer only to actual completed operand and recursive fold prefixes.
They supply no completed target or whole-worker progress law. Local general
projection and merge completion, idle warm native progress, and finite path
lists derive a complete target graph.

SourceEqualityDemandTargetWorker has separate projection-recursion, head-read,
comparison, and native-request proof bounds. It retains actual stage failures
and incomplete native observations with their full state. It does not resume
enclosing target control from an inner observation.

SourceEqualityDemandTargetWorkerSound derives every complete graph from a
checked successful worker. SourceEqualityDemandTargetWorkerComplete derives
four finite stable bounds from every complete graph. Every larger quadruple
returns its identical value and complete native state. ClassTargetAPI proves
both execution directions and uniqueness of completed graphs.

## Original physical class paths and native edits

SourceEqualityClassTarget.operandPaths uses the source ordered class paths
other than the current edited path. Coherent physical classes retain the
actual ascending path set. Nontriviality derives a nonempty other-path list.
Supported physical class paths derive proper original operand paths.

For each actual constructed target, ClassSat at the original complete term
makes every other class path select the same subterm. Target inclusion retains
that subterm. ClassTargetAPI.class_complete derives finite stable construction,
captured availability, and this language law from actual-prefix word checks.

SourceEqualityConstructedClassEdits.Constructed retains literal demanded
target receipts. Each receipt's actual returned cache grows into the common
edit base. The receipts derive closed target availability there. They replace
a supplied target language law and derive the captured scope needed by the
existing native class edit theorem.

class_exact states that terms satisfying the original class have equivalent
forest acceptance before and after these native class edits. class_complete
derives finite stable edits and that same no-loss law from actual-prefix edit
word checks. This theorem still takes concrete construction receipts at the
captured base. It does not schedule first target forcing through edit leaves.

## Next actual caller boundary

Model shared target closures at native edit leaves. Each closure captures its
class input forest. First force must execute Target and store its physical
value. Later leaves must retain that value and avoid repeated construction.
Derive Constructed witnesses from actual prefix effects at each first force.
Do not assume eager construction of every target before class editing.

Then compose the actual selected class order, class right fold, and structural
empty propagation. Reuse the existing selected/required-path graphs. Full
one-pass source correspondence, open contexts, repeated fixed points,
getAllAtPath, native containers, GHC lazy scheduling, and extraction remain
separate. The modeled demand order is not a verified GHC extraction theorem.
The Lava paper's termination assumption is not used.

## Kernel checks and validation

The empty target invokes no operand or native request. source_demand_order
checks second, third, first demand order for three original paths, followed
by the two right-fold intersections. warm_demand_reuse performs actual
projection and general merging of three constructed constant operands. It
checks one warm node memo cell, unchanged constructor heap, identical larger
bound results, and repeated demand in the returned warm state.

All twelve modules compile. The aggregate audit passes 1,727 jobs and 46,889
dependency checks using only propext, Classical.choice, and Quot.sound.
Only the older unused inputs warning remains.
Log: `/tmp/mcfta-demanded-targets-20261015-audit.log`.
Snapshot: `/tmp/mcfta-demanded-targets-checkpoint-20261015-0546/`.
It retains 2,129 Lean-tree files and four root documents. Older proof bytes
are unchanged except audit imports. Repros, counterexamples, marked drafts,
stashes, other worktrees, and production source remain unchanged. No Haskell
source changed. The earlier 645 examples and formatting checks apply to the
byte-identical tree and were not rerun. Weekly allowance was 16% at
05:46 CEST. Stop all work at 1% or less.

Exact Sized classes, finite size execution, size order, both distinct-term
rank inverses, reference and solver contracts, and optimized dispatch remain
intact. The optimized interned core remains in use.
