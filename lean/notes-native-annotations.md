# Native intersection and source path annotation preservation

Updated: 2026-10-15 07:30 CEST.
Proofs: `da6e72e7`, `ab156db1`, and `854bd6d3`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
The retained traversal repair is `61f2c939`. Continue on `formalize`.

## Actual compiled native continuations

SourceRecursiveIntersectionAnnotationCode.Certified checks actual source code.
At work instructions it checks preservation at the literal returned heap.
At optional binders it checks the available body. Node and edge requests retain
actual readiness and all continuation scopes from the existing safety proof.
It does not replace the actual machine, memo table, or source compiler.

annotation_bind and annotation_walk retain those checks through ordered calls.
Literal makeEdge checks its emitted guard. makeNode and makeUnion emit no guard.
SourceRecursiveIntersectionAnnotationCalls derives certificates for compileMu,
compileReference, compileEdge, compileRows, and union. AnnotationCompile derives
compileNode. Edge compilation checks actual source Top and conjunction results.

SourceRecursiveIntersectionNative.Bounds.annotation_heap follows completed native
evaluation. It retains actual checked keys and each returned full native state.
Direct bodies, started node and edge bodies, ready memo hits, completion frames,
and later continuations are included. BodyCode excludes standalone completion
frames. Native safety and validity supply physical scopes independently.

The optionalBinder case calls the stored-syntax annotation theorem on the
actual available body. It derives the returned heap through actual construction.
No compiled-syntax annotation law or final annotation heap is a premise.

## Exact public scoped intersection

SourceEqualityNativeAnnotationScoped.step preserves an arbitrary physical edge
annotation heap when actual emitted empty and conjoined guards satisfy it.
It obtains Bounds from the actual completed source request and reached word
checks. It supplies no successful future evaluation or final heap invariant.

public_product fixes Symbol and Guard to complete source labels and constraints.
It uses the actual Top payload and structural-order conjunction. Existing
constructor theorems derive cached normalized equality classes for every emitted
guard. The actual scoped request supplies physical result availability, closure,
and the independent PCS intersection law. AnnotationHeap.available derives
annotations for both inputs and the result from their actual linked records.
AnnotationLanguage.public_eq then gives the exact public product law for every
ambient environment and term. Both sides use acceptsConstraint.

complete combines this result with existing finite actual source completion.
Only the existing reached native word checks remain explicit. The theorem
neither assumes arbitrary raw public conjunction laws nor changes source code.
The singleton-storage boundary and all old guard proofs remain unchanged.

## Repaired reads and required paths

SourceEqualityAnnotationUnfold proves physical annotation preservation through
actual repaired stored substitution. execute and unfold cover every constructor
outcome, including pending. Original available values derive encode_allowed.
The source construction theorem preserves the returned heap.

SourceEqualityAnnotationExposure follows the actual repaired cold worklist.
collect_heap covers every bound, including exhausted observations. It retains
actual unfolding scopes and earlier decoded semantic facts. nodeEdges_heap
covers both direct ordinary reads and recursive closure reads.

SourceEqualityAnnotationHead.head retains that returned heap through the
literal final makeNode. SourceEqualityAnnotationRequired proves node, children,
and rows by mutual graph induction. Every rebuilt row obtains its full original
guard check from its actual resident edge record before child traversal.
Existing execution and effect theorems derive all intermediate available inputs.
The proof never assumes the result annotation heap.

## General source projection

SourceEqualityAnnotationProjection.read and readAll follow actual operand reads.
union reads every operand in source order, then performs one literal makeNode.
It is the actual closed source union, including its cache effects.

node and rows follow the complete mutual projection graph. Selected children
use their returned cache. Missing positions make no request. Recursive heads
use actual repaired exposure. forest covers root union, missing signed indexes,
and selected node projection. These theorems retain the same physical annotation
heap through complete traces without replacing source projection semantics.

## Remaining complete-pass boundary

This checkpoint closes public output readback for scoped native intersection.
It does not establish that readback for a whole source equality pass. Existing
NormalizedEntry.source_edges still has exact PCS output/public input meaning.
Its stronger public/public version needs every actual prefix to preserve the
annotation heap.

Next prove actual SourceMergedWorker comparison, selection, retained columns,
small and large groups, and root annotation effects. Successful comparison reads
can allocate repaired Mu records. Include these effects. The large merge branch
emits actual Top; small rows retain original full constraints. Then compose
TargetOperand, DemandTarget, shared first force, and reuse before SharedEditGraph.
Keep original captured forests, physical target slots, and warm native tables.

Carry annotations through source gate queries, required selection, class folds,
one-pass execution, and literal guarded-edge reconstruction. Derive public output
readback from the final linked heap. Do not supply a whole-merge invariant,
completed edit language, or final annotation heap as an assumption.

Inherited descendant processing, complete reducePartially traversal, open
contexts, repeated fixed points, getAllAtPath, native containers, GHC lazy
scheduling, and extraction remain separate. Sized exact classes, finite size
execution, size order, both rank inverses, and the optimized core are retained.

## Validation and preservation

All ten new modules pass focused Lean 4.34.1 builds. The aggregate audit passes
1,799 jobs and 47,752 theorem dependency checks. Only propext, Classical.choice,
and Quot.sound occur. Only the older unused inputs warning remains.
Log: /tmp/mcfta-native-annotations-20261015-audit.log.
Snapshot: /tmp/mcfta-native-annotations-checkpoint-20261015-0730/.
It retains 2,207 Lean-tree files and four root documents. Older proofs except
audit imports, all counterexamples, marked drafts, production source, stashes,
and other worktrees are unchanged. The earlier 645 Haskell examples and formatter
checks apply to the unchanged source and were not rerun.

The Lava paper's function and graph method applies to the native execution
proof. It does not discharge actual source annotation, GHC scheduling, or
extraction obligations. No Lava or Rocq dependency is added.
