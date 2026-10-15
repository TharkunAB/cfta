# Exact required-path filtering and physical caller composition

Updated: 2026-10-15 03:28 CEST.
Proofs: `68128dd5` and `cfc38752`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
The retained source repair is `61f2c939`. Continue on `formalize`.

## Current simultaneous edit checkpoint

`5635846d`, `28bf4f0e`, and `96653514` derive the signed edit compiler,
independent conditions, physical graphs, finite traversal from stored leaf
contracts, and exact stable graph/execution agreement. Read
[the current note](notes-edit-execution.md). Actual output-language agreement
and concrete narrowing callback contracts remain the next target.

## Node and row meaning

`SourceEqualityRequiredLanguage.node_exact` proves the full independent
language filter law for every completed physical RequireNode graph. The
Needed trie is valid and recursively nonnegative. The input is closed and
available in a SemanticReady cache. No whole-node callback law is supplied.
The theorem permits retained raw binders and root unions.

The mutual graph induction also proves exact child and row languages.
Empty requirements preserve the original node. Empty nodes accept no terms.
The ordinary case uses the actual makeNode language theorem after the actual
row graph. Canonical readback and removal of literal empty children remain
in that theorem. The recursive case composes the independent head theorem
with the graph body at its actual returned cache.

Each kept row retains its symbol, full guard, and actual ordered child
payload through makeEdge_fields. The maximum-key test rejects before child
work. A matching term supplies its original arity and passes that test.
The proof does not assume a row-rejection language law.

`SourceEqualityRequiredForestMeaning.Required` checks selected requirements
at each original child position. required_exact gives indexed lookup.
required_zero gives signed map-member readback. fold_exact applies the
existing signed right-fold theorem to languages, with semantic intersection
as its callback. checked_exact uses checked_row_exact and the actual row
arity check to obtain full trie matching. No physical identities from
different caches are equated.

## Compiled worker API

`SourceEqualityRequiredAPI.node_done` connects a successful instrumented
node run to the independent filter law. requireAll_done proves the exact
conditional forest law for actual compiled child runs. complete derives
finite stable execution, all final closed/resident invariants, both cache
histories, final semantic heaps, and that language law.

The source theorem starts at original closed syntax. It derives construction,
stable required-node execution, final semantic heaps, and exact source-term
acceptance conjoined with existence of every complete input path.

The top-level source child-list fold ignores a missing root position. It has
no row rejection at that level. ForestRequired therefore imposes requirements
only at present positions. requireAll_paths gives the full path-existence
law under a root arity bound. requireAll_keep derives that bound from the
accepted term and its existing paths. No global arity premise is needed for
the pure pass's preservation law. Narrowing follows from requireAll_done.
missing_root_boundary checks an empty forest and a nonempty high path.
It proves successful unchanged execution and failure of full trie matching.
This is a source boundary, not a new production failure or repair.

## Physical selection and returned caches

`SourceClosedGateCache.node_state` follows actual ordered gate graphs.
Closed ordinary records have closed children. A closed Mu cannot enter the
open-unfold branch. Every completed node, child, path, and class query on
these inputs therefore returns the original constructor cache. Selection
preserves this identity through all original class occurrences.
selection_semantic derives every SemanticReady field after selection.
It does not identify the gate Ready predicate with required-path readiness.
The result applies to closed forests. Open internal contexts still need
their actual semantic effect theorem.

`SourceEqualitySelectedRequired.paths` forms the ascending natural path-set
union and converts indices to signed values. paths_nonnegative derives all
recursive Needed premises. lookup_natural and paths_exist retain exact
complete-path readback. Native Set and IntMap representations remain outside
this source-model theorem.

Execution pairs the actual ordered selection trace with a successful required
run in its returned cache. exact derives final semantic readiness and the
independent output forest law. narrow_keep derives the two required-operation
laws used by EqualityReduction. complete retains both actual source memo
receipts and finite stable bounds for both stages. source_edges starts at
original closed source construction. In the actual live precheck branch it
derives the physical selection entry receipt, required execution, final
semantic heaps, and the independent forest law. Earlier entry theorems retain
the unchanged and contradiction branches and actual array normalization.

These are source-model constructor equations and logical call graphs.
They do not prove native lazy allocation order or verified Haskell extraction.

## Validation and preservation

All five new modules pass focused builds. The full audit passes 1,646 jobs
and 45,714 theorem dependency checks. Only propext, Classical.choice, and
Quot.sound occur. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-required-filter-20261015-audit.log`.
No Haskell source changed. The previous 645 examples and format checks apply
to the byte-identical source tree; they were not rerun for pure Lean proofs.

Snapshot: `/tmp/mcfta-required-filter-checkpoint-20261015-0328/`.
It retains 2,038 Lean-tree files and four root documents. The only older Lean proof change is added
audit imports. All repros, counterexamples, marked drafts, stashes, and other
worktrees remain unchanged. Production source remains byte-identical.
Weekly allowance was 18% at 03:28 CEST. Stop at 1% or less.

## Next source correspondence target

Model the actual signed Edits trie and insertEdit right fold. Empty-path
callbacks replace the subtree. A deeper insertion under EditAt retains that
leaf. Preserve prefix shadowing and original source ordering. Negative and
out-of-range child positions stay unchanged.

Derive actual editNode, editList, and row call graphs. Reuse exact completed
head normalization for Mu and Union heads, actual edge/node reconstruction,
and the semantic-cache invariants. Finite edit depth supplies the recursive
measure. Derive callback availability, closedness, and finite completion
from the concrete operations that the equality caller supplies.

Prove simultaneous edit narrowing and preservation. Then derive the actual
getPath, merged alternatives, intersection-list, and edit target contracts.
Use the existing physical operation proofs. Merge is an over-approximation;
do not replace its inclusion law with equality. Reuse the completed unary
ancestor theorem; preserve its archived draft.

Compose those contracts with the ordered class right fold and empty-child
propagation. Full one-pass correspondence, open contexts, repeated fixed-point
reduction, native containers, lazy scheduling, and extraction remain separate
obligations. Preserve all exact Sized sequence and inverse laws.
