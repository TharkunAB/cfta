# Selected class right fold and final literal empty propagation

Updated: 2026-10-15 06:25 CEST.
Proofs: `fe3c4cc4`, `b0c47ec2`, and `2d7eced9`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
The retained traversal repair is `61f2c939`. Continue on `formalize`.

## Source schedule correction

cfta/src/Data/CFTA/Equality/Operations.hs uses
propagateEmptyNodes $ foldr reduceEClass withNeededChildren eclasses.
Propagation runs once after the entire class fold. Earlier restart guidance
incorrectly placed it after every class. This note and the current root
restart section supersede that guidance. The earlier class-local sharing
proofs remain unchanged.

SourceEqualityClassFoldGraph.Class captures its actual current forest and
starts unforced target slots over its native entry. Fold.cons first runs the
right-hand tail and then the earlier class. The earlier class captures that
returned forest, not the original pre-fold forest. It retains the same full
native state. The returned target slots remain class-local and do not pass
to the next class. Pass applies one final propagation to the completed fold.

## Final empty propagation

SourceEqualityEmptyPropagation uses the existing literal source predicate
and erase operation. It proves exact independent ordered forest language.
An accepted tuple cannot have a literal empty child. If an empty child exists,
both the input and erased forest reject every complete tuple. The operation
preserves arity and physical closed availability and has no cache effect.
It does not unfold a recursive node or decide whether its language is empty.

## Finite fold effects and language

SourceEqualityClassFoldEffects derives local fresh-class scope from actual
shared edit receipts and the actual captured heap. It composes idle native
validity, semantic heaps, both histories, and closed output scope across the
right fold. Final propagation retains that exact native state.

ClassRanges keeps reached shared leaf checks for a fresh class. Ranges.cons
checks each earlier class only after an actual completed tail graph returns.
SourceEqualityClassFoldComplete derives each finite class, the complete fold,
and final propagation from these local checks. It requires no completed fold,
whole-class callback law, or hypothetical future cache.

SourceEqualityClassFoldLanguage composes independent output inclusion and
retention of each class-satisfying term. Every accepted input forest term
that satisfies all selected classes survives the complete fold and final
propagation. No theorem claims that one pass enforces every original equality.
The original guard must remain attached to the rebuilt edge.

## Executable workers

SourceEqualityClassFoldWorker executes class-local captures, the literal
right-fold control, and final propagation. Incomplete class observations retain
the actual original capture and shared worker observation. They do not resume
enclosing fold control.

SourceEqualityClassFoldWorkerProofs derives checked successful function-to-graph
agreement and five finite stable bounds from every complete graph. Every larger
edit, projection, head, comparison, and native bound tuple returns the same
forest and complete native state. ClassFoldAPI exposes both checked execution
directions, uniqueness of fold and pass outputs, and finite stable completion.
Class-list recursion is structural and needs no extra proof fuel.

## Physical selection and the required native entry

SourceEqualitySelectedRecords.keep aligns each original physical record with
its actual Boolean gate query. Its output is an original ordered sublist.
The selected record paths equal the selected query paths. Coherent trie fields,
nontriviality, and repeated clear occurrences remain intact. It does not rebuild
physical tries from selected path lists.

SourceEqualitySelectedNativeScope derives the actual constructor history and
closed required outputs from existing selection/required receipts. Closed gate
queries return their original constructor heap. The required worker advances
its literal returned heap inside the same native state. Existing domain and
both native memo tables remain intact.

SourceEqualityNativeInitial derives idle native validity from the actual
semantic constructor heap with empty domain and native memo tables. It does
not assume a completed native request or target language.

## Selected live-branch composition from original construction

SourceEqualitySelectedClassFold.Execution retains both actual stage receipts:
selection/required paths on the original forest and the physical selected class
Pass at their actual returned heap. Effects derive all final native, semantic,
cache-history, and closed output invariants.

The language theorem proves output inclusion and retention of every accepted
term satisfying the selected classes. Nontrivial ClassSat derives existence of
every selected required path. Under all original record constraints, original
and output forest membership are equivalent.

SourceEqualitySelectedFoldSource.complete derives actual source gate memo
receipts, finite stable gate and required-path bounds, the complete native
fold graph, and stable five-bound native execution. Its source_edges theorem
starts with original closed construction and the actual live precheck branch.
Construction supplies source children, semantic heap, and cold native validity.
Only native word checks at reached actual prefixes remain explicit.

These are complete graph compositions and component worker proofs. The final
single executable one-pass wrapper, its unchanged and contradiction branches,
array normalization agreement, and exact guarded-edge rebuilding remain the
next source correspondence target. The unchanged branch must return immediately;
it must not run final propagation on a preexisting empty child forest.

## Kernel checks and audit

SourceEqualityClassFoldExamples verifies rightmost-first order and final-only
empty propagation. Two repeated nontrivial classes each capture a two-row
forest and construct their own targets. They retain one warm native node memo
cell and return identical full native states at larger bounds. A subsequent
class with zero projection bounds attempts an actual first target projection;
it cannot reuse the previous class's target slots. Record selection retains
clear repeated occurrences. Evaluation uses kernel cbv.

All fourteen new modules pass focused builds. The aggregate audit passes
1,759 jobs and 47,301 theorem dependency checks. Only propext, Classical.choice,
and Quot.sound occur. Only the older unused inputs warning remains.
Log: /tmp/mcfta-selected-class-fold-20261015-audit.log.
Snapshot: /tmp/mcfta-selected-fold-checkpoint-20261015-0625/.
It retains 2,163 Lean-tree files and four root documents. All older proof bytes
except audit imports, all counterexamples, marked drafts, production source,
stashes, and other worktrees are preserved. The earlier 645 Haskell examples
and formatter checks apply to the unchanged source and were not rerun.

## Next target and limits

Implement physical-record selection and the combined native one-pass worker.
Compose actual prechecks and array normalization, immediate unchanged and
contradiction returns, source gate selection and memos, required paths,
fresh class captures, right-fold native requests, and one final propagation.
Derive stable bounds and checked graph/function agreement for all phases.
Then rebuild the original guarded edge and prove exact independent language.

Keep reached word checks explicit. Whole Haskell one-pass correspondence,
open contexts, repeated fixed points, getAllAtPath, native containers, GHC lazy
scheduling, and extraction remain separate. The explicit fold worker gives
one logical execution schedule. Its function/graph agreement does not prove
that GHC uses that heap demand or allocation schedule. Lava's graph method
helps state the proof; its assumed termination and call-by-value theorem do
not supply lazy Haskell correspondence or these independent finite bounds.
