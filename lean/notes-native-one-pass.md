# Complete guarded native one-pass equality worker

Updated: 2026-10-15 06:47 CEST.
Proofs: `565ea4a4`, `b859a782`, and `ed3568fe`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
The retained traversal repair is `61f2c939`. Continue on `formalize`.

The actual guarded-edge reconstruction target below is now proved in
[the guarded-edge note](notes-guarded-edge.md). Actual own readback derives
physical validity and satisfaction. The generic guard-constructor contracts
still require a proof restricted to normalized actual reached guards.

## Physical record selection

SourceEqualityRecordSelectionWorker.queries runs the actual classMeets worker
on each original physical record in source order. Each returned query retains
its path set, entry heap, Boolean, and returned heap. Failed or exhausted gate
work remains its actual source observation. select filters the exact original
records with these actual query positions. It retains repeated clear occurrences.

SourceEqualityRecordSelectionProofs proves successful query execution gives
the existing ordered source Trace. Every complete Trace supplies a finite
query bound. Every larger bound returns the identical queries and heap.
The selected record paths equal the existing source selector's selected paths.
No physical trie is rebuilt from a selected path list.

## Complete guarded worker and graph

SourceEqualityOnePassGraph.Graph retains checked error, unchanged,
contradiction, and live branches. Execution uses the actual source precheck.
Ranges checks native words only in the live branch after actual completed
selection/required receipts. The other branches require no native range plan.

SourceEqualityOnePassWorker implements the same complete control. Immediate
unchanged returns retain the original child list, even if it contains an empty
child. Contradiction erases every original position. The live branch selects
original records, requires their complete path union on the original forest,
then runs the native class right fold with fresh class-local target slots.
It propagates literal empty children once after the entire fold.

The source worker retains exact checked errors and incomplete selection,
required-path, and native narrowing observations. Returned constructor heaps
advance in the same full native state. Domain and both native memo tables
remain at their actual values. Incomplete stages do not resume enclosing control.

## Finite bounds, two-way agreement, and array entry

SourceEqualityOnePassWorkerProofs proves checked successful execution gives
the full source graph. Every complete graph supplies six finite bounds:
gate queries, edits, projection/required recursion, head reads, comparison,
and native requests. Required paths and target projection share one bound.
The maximum of their local bounds suffices. Their head reads share another.
All larger tuples retain the identical answer and complete native state.

OnePassAPI exposes both execution directions, uniqueness, source-entry
stability, and actual array-entry stability. precheckArray_eventual supplies
an additional independent parent-array bound. Every larger array bound and
every sufficient stage tuple returns the same source answer and native state.
No successful whole-pass run is supplied to derive these finite bounds.

## Native effects and independent language

SourceEqualityOnePassEffects derives idle native validity, semantic constructor
heaps, cache histories, and closed physical outputs through every successful
branch. Immediate branches leave native state unchanged. Live effects compose
the actual selected/required receipts with the native fold and final propagation.

SourceEqualityOnePassPrecheck derives rejection from the actual combined
normalization semantics. A term satisfying both original payloads cannot
reach contradiction. Live ordering retains every original own class and its
satisfaction. Valid requires coherent nontrivial own records. It is a physical
payload invariant; it is not a supplied callback or whole-pass language law.

SourceEqualityOnePassLanguage proves output forest inclusion and preservation
of every accepted term satisfying both original own and inherited payloads.
The original complete guard remains to be connected at actual edge rebuilding.
The theorem does not claim that one pass enforces all original equalities.

## Original source completion and both gate memos

SourceEqualityOnePassSource.complete derives every source precheck branch from
its actual safe precheck result. The live case derives gate and required-path
completion, actual source memo read receipts, and the native fold from reached
word checks. Cold native validity follows from the actual semantic constructor
heap. The source_edges theorem starts from original closed construction and
supplies complete one-pass source execution for each original outgoing child
forest. It supplies no completed whole-pass run or global leaf law.

StageMemos retains both SourceMemoClassSelection.Reads call graphs and actual
SourcePredicateGateTrace.Keeps validity. MemoReads is an indexed certificate
for the complete graph. Immediate branches have no query; live certificates
retain their literal stage receipts and both returned source memo families.
Both source and bounded-array entries have finite stable complete answers.

## Kernel checks

SourceEqualityOnePassExamples proves zero-bound immediate unchanged,
contradiction, and checked-error returns. The unchanged branch preserves a
mixed empty/unresolved forest. A live empty class list instead performs the
single final propagation. This checks the real distinction between the guards.

The complete ordinary fixture retains actual selection, required paths,
target construction, native requests, and final propagation. It returns one
warm native node memo cell. Larger six-bound tuples and repeated warm runs
return identical full states. Its guard is proved from the actual normalizer's
semantic theorem. A local cbv_eval lemma identifies the specialized source
entry with that checked branch. Kernel evaluation then checks the remaining
actual stages. This compositional check takes about one second and avoids
expanding a large normalization proof inside the full fixture. General array
agreement is proved for every sufficient array bound; one fixed numeric array
fixture is not used as a substitute for that theorem.

## Validation and preservation

All eleven new modules pass focused builds. The aggregate audit passes
1,770 jobs and 47,483 theorem dependency checks. Only propext, Classical.choice,
and Quot.sound occur. Only the older unused inputs warning remains.
Log: /tmp/mcfta-one-pass-20261015-audit.log.
Snapshot: /tmp/mcfta-one-pass-checkpoint-20261015-0647/.
It retains 2,175 Lean-tree files and four root documents. All older proof bytes
except audit imports, all counterexamples, marked drafts, production source,
stashes, and other worktrees are preserved. The earlier 645 Haskell examples
and formatter checks apply to the unchanged source and were not rerun.

## Next actual source correspondence target

Connect guarded-edge rebuilding with the original symbol and complete guard.
Derive the own physical payload and its validity from the actual source
Constraint.equalities accessor. Use SourceCompactGuards.sourceEqualities,
positiveNormalized_support, normalization semantics, and physical record
construction to derive the required ClassSat facts from source guard acceptance.
Do not supply a guard-to-payload or whole-edge language law. Keep inherited
satisfaction explicit as the surrounding context. Rebuild with the literal
makeEdge request and prove exact independent guarded-edge language and stable
finite edge execution from original construction.

Keep actual native word checks explicit. Open contexts, repeated fixed points,
getAllAtPath, native containers, GHC lazy scheduling, and extraction remain
separate. The function/graph proofs concern these explicit workers. They do
not verify GHC's heap demand or allocation schedule. Lava's graph method helps
state this proof; its call-by-value theorem and assumed termination do not
supply lazy Haskell correspondence or these independent finite bounds.
