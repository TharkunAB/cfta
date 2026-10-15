# Finite physical simultaneous edit execution

Updated: 2026-10-15 03:42 CEST.
Proofs: `5635846d`, `28bf4f0e`, and `96653514`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
The retained traversal repair is `61f2c939`. Continue on `formalize`.

## Signed compiler and independent conditions

`SourceEqualityEdits.Edits Action` uses editAt for a leaf callback token and
editBelow for signed child-map entries. insert copies the source cases.
An empty path replaces the current subtree. A deeper insertion under editAt
retains the existing leaf. build retains the actual source right fold.
insert_valid and build_valid derive ascending unique child maps recursively.
insert_all, build_all, and all_mono transport leaf contracts. Kernel equalities
check duplicate paths, prefix paths in both orders, and root shadowing.

The constructor names avoid Lean's reserved at token and generated below
recursor name. They correspond to the Haskell EditAt and EditBelow cases.
Native IntMap and machine Int representation remain explicit boundaries.

`SourceEqualityEditMeaning.Matches condition edits term` gives an independent
condition at each retained leaf. A below-node applies its descendant conditions
only at existing signed child positions. It does not require missing positions
to exist. Forest checks the same conditions in original child order.
forest_exact supplies indexed readback. forest_zero identifies root traversal
with Matches for an ascending map. apply_exact and fold_exact identify the
actual signed adjustment right fold on languages with this condition.
No physical output identities from different caches are equated.

This independent predicate is not yet connected to the physical output language.
Nor is the compiler's leaf condition yet characterized by all original
nonoverlapping edit paths. Prefix and duplicate raw inputs retain their actual
compiler behavior; they are not silently replaced by a disjoint edit list.

## Physical graph and worker

`SourceEqualityEditGraph.Callback` executes a leaf operation with the existing
explicit Result type. EditNode, EditChildren, and EditRows are mutual graphs.
EditList retains the source list leaf branch separately. Each callback supplies
its actual call equation and complete returned cache in its leaf receipt.

Node leaf callbacks execute before inspecting the input node. They can run
on empty nodes or references. A child-list leaf returns unchanged and executes
no callback. A below-node has no empty-map identity shortcut: it returns empty,
reports an unresolved reference, rebuilds all ordinary rows, or exposes a Mu
or Union head before it continues. Every row retains its original symbol,
complete guard, and child order. There is no required-path arity rejection.

`SourceEqualityEditWorker` implements these branches with separate recursive
worker and cold-head bounds. It keeps pending constructors, unresolved
references, and both exhausted limits. Leaf callback outcomes remain explicit.
The worker bound instruments the traversal only. It does not bound internal
callback work. The child scan and source right fold concern returned results;
they do not prove a native lazy callback allocation order.

## Completion, agreement, and source entries

`SourceEqualityEditComplete.CallbackComplete call action` is the explicit
per-leaf completion contract. For a closed available input in a SemanticReady
cache, it gives actual completed callback execution, Keeps, SemanticReady,
available output, and closed output. The concrete equality caller still must
derive this contract for its actual intersection target callback.

The child and row completion proofs derive every intermediate cache from
the stored child induction hypotheses. Actual edge and node constructors
supply all remaining effects and readback. The node proof decreases strict
finite edit-trie size. Mu and Union nodes use complete actual head exposure,
then the ordinary helper. Automaton nodes can remain cyclic. No whole-worker
completion or productivity premise is supplied.

`SourceEqualityEditWorkerSound` proves that every successful instrumented run
has its complete exact graph. It needs no Ready, callback completion, or
success assumption for another worker. Failure outcomes cannot produce a
successful graph. `SourceEqualityEditWorkerComplete` proves the converse.
The mutual graph recursor derives a pair of sufficient bounds. All larger
pairs return exactly the graph's result and final constructor cache.

`SourceEqualityEditExecution` derives node uniqueness, both-direction node
agreement, compiled-list agreement, and stable list execution. node_verified,
children_verified, and rows_verified use certified completion plus exact
execution uniqueness. They derive semantic heaps, both histories, and the
closed/resident final payload for any successful graph from its leaf contracts.
No invariant for the whole output is supplied.

The source theorem starts at original closed syntax. source_edges derives the
compiled list theorem for each actual original ordinary edge. Both source
entries derive every initial cache and closure premise. The original leaf
callback completion contracts remain explicit.

## Kernel fixtures and preservation

`SourceEqualityEditExamples` checks node/list leaf branch priority with a
callback that has a visible unresolved result. Negative and high signed child
positions leave the forest unchanged at zero worker fuel. The actual retained
raw self binder normalizes to empty with worker bound two and head bound two.
Each smaller bound reports the correct exhausted limit. A root list leaf
does not visit that binder. All fixtures use kernel reduction.

The full audit passes 1,655 jobs and 45,879 theorem dependency checks.
Only propext, Classical.choice, and Quot.sound occur. The only warning is
the older unused inputs binder. All nine new modules pass focused builds.
Log: `/tmp/mcfta-edit-execution-20261015-audit.log`.
No production Haskell source or formatter input changed. The previous 645
examples and format checks apply to the byte-identical tree; they were not rerun.

Snapshot: `/tmp/mcfta-edit-execution-checkpoint-20261015-0342/`.
It retains 2,048 Lean-tree files and four root documents. The only older proof
file change is added audit imports. All repros, counterexamples, marked drafts,
stashes, other worktrees, and production source remain unchanged.
Weekly allowance was 18% at 03:42 CEST. Stop at 1% or less.

## Next: language agreement and concrete narrowing callbacks

Prove actual output-language agreement by the mutual edit graph recursor.
For narrowing callbacks with exact per-leaf language contracts, derive:

meaning result term iff meaning input term and Matches condition edits term.

Use a valid trie, closed available input, and SemanticReady before. Each leaf
must retain its actual callback equation. node_verified and the two list
verified theorems supply all intermediate cache and closure facts from leaf
completion contracts. head_exact supplies the recursive branch. Actual
makeEdge_fields and makeNode_exact supply ordinary row readback. forest_zero
gives the independent below-node condition. No nonnegative-key premise is
needed for edits: negative positions are conditional no-ops.

Derive the compiled predicate for original nonoverlapping edit paths. Keep
raw prefix shadowing and duplicate callback priority explicit. Then derive
the concrete intersection, getPath, merged-alternative target, and callback
completion/language contracts. Reuse existing physical operation proofs and
the completed unary ancestor theorem. Merge is an over-approximation, not an
exact transformation. Do not promote a conditional callback theorem to a
complete native equality pass.

Compose these results with the completed required-path and ordered selection
stages, the source class right fold, and empty-child propagation. Full one-pass
correspondence, open internal contexts, repeated fixed-point reduction, native
containers, lazy scheduling, and extraction remain separate obligations.
Preserve all exact Sized sequence and both inverse laws.
