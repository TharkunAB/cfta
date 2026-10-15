# Concrete inherited edge continuation and indexed children

Both filtered Mu probes now have an explicit physical heap invariant. Actual
source and native execution, reads, merging, targets, shared edits, and complete
guarded passes preserve it. The returned heap supplies exact outer Mu execution.
Next use mutually recursive completed outer graphs to obtain actual child
induction hypotheses, then prove bounded worker agreement and replay. Carry
the probe invariant explicitly; current IdleReady does not contain it. Read
[the current note](notes-filtered-probes.md). This paragraph supersedes older
probe propagation and unrestricted callback targets in this note.

The actual outer worker, ordered rows, modifyNode fast path, and cached Mu
reconstruction are now checked. Successful outer steps derive their local
language and scope conclusion. The smaller recursive callback and reached
physical checks remain explicit. The next target is probe-invariant propagation
and traversal-bound induction. Read [the current note](notes-partial-node.md).
This paragraph supersedes older outer traversal and Mu targets in this note.

Updated: 2026-10-15 08:01 CEST.
Proofs: `55fd6fed`, `0f8c72b5`, and `07410acf`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
The retained traversal repair is `61f2c939`. Continue on `formalize`.

## Actual physical descendant constraints

SourceEqualityDescend.record follows pathEClassDescendNontrivial. It descends
the original trie at one natural child index, runs the existing structural
pathTrieHasAtLeastTwoPaths scan, and retains only nontrivial suffix classes.
fromTrie uses the actual fromPathTrie path enumeration for the lazy source set.
records keeps literal empty and singleton branches and runs the actual source
sortBy schedule for larger lists. It compares ascending path sets, rather than
using the subsumption order used by local class selection.

The older EqualitySaturation structural scan matches the live source and is
reused. No second scan model or new normalization replaces source descent.
records_perm retains every selected record occurrence through sorting.
record_pairs and descend_exact prove exact same-child suffix equality meaning.

WellFormed combines coherent record fields, ascending trie maps, and nontrivial
classes. Ascending maps establish the source Set.fromDistinctAscList precondition.
canonical_fromTrie proves that valid ascending trie enumeration already has the
canonical path-set order. recordOf_ascending and recordsOf_ascending derive these
maps from the actual original constructors. record_wellFormed and
descend_wellFormed retain the invariant. descend_sound supplies the actual child
payload for every selected term position. This uses the existing supported
nonnegative physical path domain; caller zip indexes are natural.

## Source combination and accessor readback

SourceEqualityInheritedPayload.classes reads the physical class path lists.
read_wellFormed derives ascending maps from actual normalized physical readback.
read_complete supplies finite source construction and exact payload meaning.

combine runs the actual source combiner with inherited records first and local
records second. combine_complete derives physical output and exact conjunction
without a normal-form premise on those raw input payloads. combine_exact gives
the same facts for any actual completed receipt. combine_readback connects it
to the existing complete precheck normalization result.

combineArray retains bounded normalization timeout as none. It does not treat
an exhausted observation as contradiction. combineArray_eventual proves the
same combined physical answer, including checked errors, at every sufficient
actual array work bound. own_complete uses the complete source guard accessor
and derives local satisfaction from public acceptance. combined_child composes
these facts with the actual descendant constraint.

## Indexed source children and exact observations

SourceEqualityInheritedChildren.Result retains completed checked answers with
their full native state. Incomplete observations keep their original type and
value. The observation universe permits the existing native source stage types.
Result.bind resumes only successful callbacks. Errors and incomplete observations
are returned without running the enclosing continuation.

walk follows source zipWith indexes from zero. Every callback receives
SourceEqualityDescend.descend payload index, and the next callback starts in the
exact native state returned by its predecessor. run handles EqContradiction by
mapping every child to EmptyNode without any recursive request.

Walk and Graph retain actual callback receipts and full states. Walk.execute,
walk_graph, and execution_iff prove two-way worker/graph agreement. Walk.length
and Graph.length prove unchanged child arity. walk_error and walk_incomplete
retain literal first-callback observations without invoking the tail.

SourceEqualityInheritedChildrenProofs.Callback is the local recursive node
induction hypothesis. It concerns one actual successful node call at its own
closed available input scope. It remains an explicit premise. It must be derived
by the future outer caller proof. It is not a proof of that caller.

walk_verified advances every available child through actual histories and derives
final idle native validity, output scope, closure, and annotations. Its pointwise
forest induction uses each child term at its actual offset. parent_obligations
supplies precisely that child's descended payload from parent satisfaction.
live_exact and graph_verified include narrowing, contextual exactness, and the
contradiction branch. No whole-child-forest preservation law is supplied.
setChildren derives the actual source equal-arity direct interning branch for
any checked fallback. Source symbols and complete constraints remain unchanged.

## Concrete inherited edge composition

SourceEqualityInheritedEdge.Graph is the actual reduceChildren continuation.
It retains actual own accessor readback, inherited/local combination, indexed
child receipts, and literal full-constraint edge allocation. Graph.verified derives
native scope, both histories, residency, closed children, annotations, exact
labels, public narrowing, and public exactness under inherited satisfaction.
Guard acceptance supplies local satisfaction through the proved actual accessor.
The recursive node Callback remains the only local traversal induction premise.

Execution first runs the concrete SourceEqualityPCSNativeEdge local native pass,
then this inherited continuation. Execution.language composes the already proved
public local edge theorem with the new child processing law. It supplies no
generic EqualityReduction.Laws, binder law, or whole-edge language law.

SourceEqualityInheritedEdgeWorker.descendants implements physical accessor,
combination, child traversal, and edge allocation. run first invokes the actual
six-bound guarded native worker with concrete source controls. It retains exact
source-stage errors and incomplete observations without resuming them.
graph_executes, descendants_graph, run_graph, and execution_iff prove both
directions of operational agreement. stable proves identical results and full
native states at every sufficient six-stage bound for a fixed recursive callback.
This does not claim stability when that callback itself changes its traversal
bound, and it does not establish general recursive node completion.

## Remaining outer caller obligation

The full reducePartially worker is not proved here. Next build actual ordered
node and row traversal around SourceEqualityInheritedEdgeWorker. Derive Callback
by traversal-bound induction. Ordinary modifyNode must retain the original node
when returned edges are unchanged and construct the literal new node otherwise.
Use the concrete edge graph, rather than assume a complete edge language law.

The source Mu branch invokes matchMu and createMu. It reuses cached probe
observations and then applies smart cleanup. Do not replace it with node identity
or a supplied binder language law. Resident source keys, actual cached request
readback, existing guarded finish_exact, and constructor availability facts are
available. Derive the exact probe/filter and request scope before claiming this
branch complete. Explicit unions and EmptyNode return unchanged. A free Rec is
an error. Retain all incomplete and error scopes in the complete bounded worker.

General caller termination remains open. Finite local native passes do not imply
it. The original cached depth is not a general measure because intersection can
increase ordinary depth. Preserve the earlier depth and cycle counterexamples.
Open contexts, repeated fixed points, getAllAtPath, native containers, GHC lazy
scheduling, and extraction remain separate. Sized exact classes, finite size
execution, size order, both rank inverses, and the optimized core are retained.

## Validation and preservation

All six new modules pass focused Lean 4.34.1 builds. The aggregate audit passes
1,812 jobs and 47,884 theorem dependency checks. Only propext, Classical.choice,
and Quot.sound occur. Only the older unused inputs warning remains.
Log: /tmp/mcfta-inherited-edge-20261015-audit.log.
Snapshot: /tmp/mcfta-inherited-edge-checkpoint-20261015-0801/.
It retains 2,222 Lean-tree files and four root documents. Older proofs except
audit imports, all counterexamples, marked drafts, production source, stashes,
and other worktrees are unchanged. The earlier 645 Haskell examples and formatter
checks apply to unchanged source and were not rerun.

The Lava paper's explicit function and graph method applies to these actual
continuations. It does not supply the outer callback induction, runtime
scheduling, or extraction. No Lava or Rocq dependency is added.
