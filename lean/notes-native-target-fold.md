# Scoped native target folds and narrowing

Updated: 2026-10-15 04:24 CEST.
Proofs: `69de4363`, `e03f2c4d`, and `e145fe27`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
The retained traversal repair is `61f2c939`. Continue on `formalize`.

## Actual warm request state

SourceEqualityNativeScoped.IdleReady contains actual native validity, idle
memo tables, and SemanticReady for the constructor cache. It permits populated
memo tables. Step retains the actual native execution, word checks, and full
returned state. Step.verified derives all next-call premises, Keeps, closed
available results, and exact independent input-intersection-target language.
Closed operands derive Original syntax. complete applies existing idle warm
progress. It assumes no successful request execution. Step.stable returns
the same value and complete native state at every sufficient larger bound.

advanceHeap changes only the constructor heap of the actual native machine.
IdleReady.advance derives native validity and idle state from actual Keeps
and semantic heap effects. It preserves the domain cache and both memo tables.
No runtime table conversion, cache preparation, or memo reset is added.

## Exact source intersection lists

Equality/Operations.hs:194 defines intersectList [] as EmptyNode. It uses the
first operand as seed and folds the tail with foldr intersect. With three
operands, it intersects the third with the first, then the second with that
result. It does not seed the right fold with the last operand.

SourceEqualityNativeTargetFold.Fold retains each actual native Step after its
tail. IntersectList retains the empty and first-seeded source branches.
verified derives final IdleReady, both constructor histories, and closed
available results. Its independent language equals the conjunction of all
operands for nonempty lists. ListMeaning is false for an empty list.
All intermediate operands remain available through actual prior cache growth.

FoldRanges and ListRanges retain machine-word premises at the actual request
states. A FoldRanges step checks each completed smaller tail graph and its
returned full state. It does not quantify arbitrary unrelated heap extensions.
fold_complete and complete use finite list length and local warm completion.
They do not assume whole-fold termination or reset native memo tables.
Word-range premises remain a concrete machine-representation boundary.

SourceEqualityNativeTargetExecution.fold executes the source right fold with
a common bound on its individual native requests. intersectList keeps empty
and singleton shortcuts. Successful checked runs give the exact graph.
Every graph gives stable identical results and complete native states at all
larger bounds. execution_iff proves both directions. list_unique gives one
returned value and full state. scoped_complete carries operands from their
real earlier cache through Keeps. Bounds are proof instrumentation.
A noncompleted request returns its actual observation. The outer fold worker
does not claim resumable outer control from that inner native observation.

## Projection and one target application

SourceEqualityNativeProjection.forest_effects derives every immediate cache
premise from actual general forest projection. forest_lift and forest_complete
advance the retained native state. They preserve domain and both memo tables
by literal equality. Captured original forest values remain available through
actual Keeps. Stable projection execution and independent subterm inclusion
come from the general getPath proof. No projection or whole-worker law is
supplied by the caller.

SourceEqualityNativeTargetNarrowing.Narrow describes one target-list
construction followed by one actual native request at its returned state.
verified derives exact input language intersected with ListMeaning for the
original operand list. complete derives finite execution from the scoped
actual-prefix word checks. The input remains available through target
construction. scoped_complete retains an earlier actual scope for input and
operands. This is one construction and one application. It does not yet model
shared target forcing across repeated leaf occurrences in simultaneous edits.

## Kernel checks and validation

SourceEqualityNativeTargetExamples proves empty and singleton lists complete
at bound zero. source_order retains the exact three-operand request order.
warm_reuse evaluates real native requests with cbv. The first request
publishes and returns one node memo cell. Two- and three-operand folds and a
later warm fold retain that identical full returned state. The edge memo
inventory stays empty in this fixture. No native evaluation axiom is used.

All six new modules pass focused builds. The aggregate audit passes 1,677
jobs and 46,148 theorem dependency checks. Only propext, Classical.choice,
and Quot.sound occur. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-native-target-20261015-audit.log`.
Snapshot: `/tmp/mcfta-native-target-checkpoint-20261015-0424/`.
It retains 2,075 Lean-tree files and four root documents. Older proof bytes
are unchanged except audit imports. Repros, counterexamples, marked drafts,
stashes, other worktrees, and production source remain unchanged.
No Haskell source or formatter input changed. The earlier 645 examples and
format checks apply to the byte-identical tree. They were not rerun.
Weekly allowance was 17% at 04:24 CEST. Stop at 1% or less.

## Next actual caller obligations

Carry IdleReady and captured-target availability through actual simultaneous
edit nodes, child lists, and row reconstruction. Use Step at real leaves and
advanceHeap after actual head/edge/node effects. Preserve actual native memo
and domain state and actual leaf word checks. The existing global LeafLaw
still quantifies all semantic-ready caches. It is not an instantiation for
arbitrary captured native targets. Preserve that conditional theorem.

Derive mergeAlternatives inclusion for independent guarded language and
SemanticReady preservation through the actual worker. Existing
MergedColdMergeSoundness proves finite cold execution and inclusion in every
later prepared common-cache graph. Its language and preparation premises
still need connection to the independent closed-source target caller.
Do not supply a whole-merger law to close this gap.

Then derive original physical class targets, complete class edit batches,
the ordered class right fold, and empty propagation. Full one-pass source
correspondence, open internal contexts, repeated fixed-point reduction,
getAllAtPath, native containers, lazy scheduling, and extraction remain open.
Preserve exact Sized classes, size order, both term-rank inverse laws, and
the optimized interned core. Preserve the completed unary ancestor theorem
and its archived draft.
