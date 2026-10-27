from pathlib import Path
root=Path('/home/tritlo/Code/mcfta')
block='''## Flat union-find now preserves complete enumeration core outcomes

Main `64cfe9fc6` is integrated at `865facc70`. The constrained extraction repair
from PR #182 is merged and locally verified. Its source and regression equal
upstream. The retained reproducer now returns the accepted cost-5 term.
All 341 core tests, changed Haskell Fourmolu and cfta Cabal-gild checks pass in Nix.
FINDINGS retains the baseline failure, stronger cost contract and repair evidence.

Stable bounds and ordered results: `b474c9f6a`.
Flat core, access and allocation: `3b491a34e`.
Assimilation and full assignment transport: `ae964e335`.
The full goal stays ACTIVE. H6 remains the strongest global language theorem.
The previous captured native rendering theorem remains unchanged too.

The new six-field core changes only the union-find representation. Related cores
retain exact counters, raw slots, obligations and both ancestry fields. Actual
representative reads and unions agree at a derived stable sufficient old bound.
Slot access, allocation, ancestry, assimilation and incoming-node merging retain
ordered successes, rejections and explicit errors. Raw source slots stay raw.
Full assignments include all forest equalities, stored restrictions and residuals;
related cores permit exactly the same assignments. No assignment existence follows.

All seven modules and Audit pass strict Lean checks. Aggregate Audit passes
3989 jobs and 78183 theorem dependency checks. Installed readback covers 34 new
public theorems, unchanged H6 and captured rendering, and 19 full definitions.
Old proof sources change only by seven Audit imports. Keep every prior draft.

Next carry the relation through native indexes, cached state, Caller and queries.
Related alone does not imply Safe, stored-address bounds or canonical indexes.
Whole recursive output soundness, discharge/rendering existence, selector coverage,
forward completeness, concrete containers and machine integers remain open.
Details: `lean/notes-current-flat-enumeration.md`.

'''
paths=['NEXT-PROMPT.md','HANDOFF.md','lean/README.md','lean/SYSTEM.md','lean/COVERAGE.md','lean/API-COVERAGE.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md']
for name in paths:
 path=root/name;old=path.read_text();first,sep,rest=old.partition('\n')
 assert sep and block not in old
 path.write_text(first+'\n\n'+block+rest.lstrip('\n'))
 assert path.read_text().endswith(rest.lstrip('\n'))
(root/'lean/notes-current-flat-enumeration.md').write_text('''# Flat union-find in the enumeration core

Published base: bdac77598165d55c4057c1dbe0f7737cd086b934.
Imported main: 64cfe9fc6fb9df5a3957ba8821fae3e88f1790ea.
Main integration: 865facc70ba6a10b6a875c60d1bb3ceb8c2d2cb3.
Stable bounds and rows: b474c9f6ae1809a6fdb4b1c70a703e7290e1012b.
Core state and primitives: 3b491a34e8db2f77ab80cbd5e93a9e3795ba9460.
Assimilation and semantics: ae964e33547a95734f350c63c7ac5409ec84b690.
The complete goal stays ACTIVE and incomplete. Keep the optimized interned core
as primary. Preserve all older proofs, counterexamples, repairs and marked drafts.
The preceding checkpoint is notes-current-flat-union-find.md.

## Strongest claims

H6, SourceCurrentColdFiniteWarmCalls.constructed_node_calls, is unchanged.
Under its formal guard and allocation assumptions, covered closed construction
supplies an actual modeled finite node-processing trace at derived mathematical
width and fuels for any chosen budget and number of rounds. With the empty
inherited payload, the final available node accepts exactly the original finite
trees in every ambient environment. This is the strongest global language theorem.
Its source SHA256 remains e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5.

The earlier CapturedEdge.diagonal_render_sound_current is unchanged too. Its
actual stable completion and stated admission, structural discharge, successful
native render and checked returned residuals give an accepted original edge
and parent term. It constructs its complete assignment and derives final Safe
and order. It does not establish whole recursive scheduler completion, discharge
or rendering existence. All its documented semantic gates remain explicit.

The new result concerns enumeration's core state. A source-shaped flat forest
backend and the earlier path backend give related complete core results for
representative access, union, raw slot reads and writes, allocation, ancestry,
raw-source assimilation and incoming-node merge. Success values are equal.
Returned states have the same five non-forest fields. Errors retain their
identity and position. Rejected branches remain empty result lists.
Related cores permit exactly the same full assignments, including slot
restrictions and residual guards. Root tests and canonical tries also transfer.

## Flat core and relation

EnumerationFlatState.State has six fields. It reuses the earlier UVarValue,
Fragment, Suspended, RecursionKey and Error types. Its forest field uses the
new direct-parent FlatUnionFind.Forest. The other fields are counter, values,
obligations, recursionAncestry and expansionAncestry.
Related requires FlatUnionFind.Valid and the exact-root-and-size forest relation.
It also requires literal equality of all five other fields, including equality
of the complete ancestry functions. No raw address renaming is used.
Initialization derives the complete relation from the two singleton forests.

Flat representative reads use current find and retain the forest. Flat union
changes only the forest. These operations need no source union-find fuel.
The earlier finite interpreter still exposes representativeFuel errors when
its bounds are too small. No arbitrary-fuel equality is claimed.

FlatUnionFindStable.find_stable returns one exact old Result outside the
forall-extra quantifier. Every larger bound returns that same result.
union_stable raises both old lookup fuels to their maximum, then extends both
by the same extra. It retains one exact old output forest. It reuses
EnumerationExecution.union_moreFuel; no second monotonicity proof is introduced.
Primitive stable theorems expose ordered Results Related at a genuine bound and
every extension. They consume those fixed old witnesses in their proofs.
The state-level statements do not export a named fixed old state separately.

## Ordered results and control flow

EnumerationResultRelation reuses Language.All2 (Lean name All₂). Outcome pairs
equal success values with related final states, or the same explicit error.
Results pairs every list position. It preserves length, order and multiplicity.
bind_rows follows actual finite flatMap and does not run a continuation on errors.
stateT_bind_rows unfolds the concrete StateT/ExceptT/List operations.
stateT_bind composes through their actual intermediate returned states.

The represented CPS theorem requires full Represents witnesses. The two primitive
CPS theorems compare flat encode with the earlier exact CPS representative and
union callers. They do not infer arbitrary CPS bind behavior from allResults
alone. The raw CPS function type does not require continuation parametricity.

rawValue retains invalidSlot exactly. setValue writes the supplied RAW variable.
getValue resolves once, then reads the same representative slot from equal arrays.
Allocation returns the same old counter, increments it and appends the same pending
slot. It inherits ancestry at that old counter. It does not insert a forest root.
An absent entry continues to denote a singleton. These are operational results;
no allocation-domain premise is silently inferred from the state relation.

Assimilation reads the raw recorded source first. It skips an eliminated source
before reading the target. Otherwise it intersects source and target, checks
emptiness, writes the target, eliminates the source, then updates ancestry.
Incoming-node merge first resolves the actual target. It writes the merged value
and inherits ancestry before its emptiness guard. Both orders match the earlier
core and the inspected source projection. The graph intersection interface is
shared; these theorems do not execute or repeat a native heap intersection.

## Assignment and invariant transport

EnumerationFlatSemantics.Satisfies combines FlatUnionFind.Satisfies,
heapSatisfies on the existing slot interpretation, and the existing guardsHold
on all residual obligations. related_satisfies proves a full iff for one fixed
supplied node language, guard meaning and complete term assignment.
No satisfying assignment or accepted term is constructed by this iff.
union_satisfies adds exactly the requested value equality and retains every
stored slot and residual restriction.

related_isRoot includes absent or unallocated variables. It does not imply that
the variable is below counter. related_supplyAligned transports only counter
being equal to the value-array length. related_canonical transports only valid
suspended tries stored in that exact array.

The relation alone does not imply Safe, ForestBound, native slot validity,
waiting-index validity or an explicit-map support bound. For example, a flat map
with an explicit singleton root at every Nat relates to an empty earlier map,
but has explicit entries above any counter. These are separate invariants.
Do not add false bounds merely by reading semantic root paths.

## Merged constrained extraction repair

During this work PR #182 merged at main 64cfe9fc6. Integration 865facc70 changed
only cfta/CHANGELOG.md, EGraph.hs and EGraphSpec.hs. There were no conflicts.
The implementation and regression sources equal upstream exactly. Old and new
upstream sources, the complete diff and merged GitHub readback are retained.
The original baseline failure remains in the preceding rendering evidence.

The merged extract returns the first termsByCost result. Its contract adds
child-cost monotonicity and retains strict increase above each child. It documents
nontermination for an infinite language whose terms all fail the constraints.
The constrained regression is added; the resulting identity property is removed.

The unchanged reproducer now returns Just (5,p(h(b),b)), the same first cost-list
term, and Right True from classAutomaton. Its exact result is 118 bytes with
SHA256 4414d3a1236d3e56c4ac279637fb7d8c71fe0d40b3a5fe3cd5188b3d1ad1e943.
The complete native build log confirms that the changed module and test rebuilt.
All 341 core examples pass with seed 20261027. Fourmolu checks of both changed
Haskell files and cfta Cabal-gild pass inside Nix. The repository instructions
require these checks. No additional runtime repair or test is authored here.
FINDINGS records the fix for external work. General e-graph, extraction-cost,
termination and opt-in pruning proofs remain outside the current system claim.

## Proof validation and evidence

All seven new modules and changed Audit pass warningAsError and linter.all in
Lean 4.34.1. Aggregate Audit passes 3989 jobs and checks 78183 theorem dependencies.
Only propext, Classical.choice and Quot.sound are permitted. The unchanged older
unused-input warning remains in InternedFreshOrdinaryClosedCompletion.lean:24.

Installed readback has 34 new public theorems, unchanged H6 and captured rendering,
and 19 complete definitions. The final readback has 46387 bytes and SHA256
39ed72cee0810bc13b8a214e9785eeb1cbce55b789351d1c42e17005e1b0c477.
Every final proof source equals its passing strict snapshot, installed source and
committed source. Earlier Lean sources change only by seven Audit imports.

Retain all strict drafts. Their errors concern maximum-bound unfolding, computed
induction indexes, explicit List instances, a slot constructor, StateT reduction,
shared type parameters, match case analysis and a namespace. The result-relation
strict2 source passed before its StateT helpers were added; strict3 is final.
The first public name scan misread a module-comment sentence as a theorem called
supplies. Removing comments corrected the inventory. Both readbacks remain.
No proof source changed to make a failed public name check pass.

Three bounded exact-source reviews report CLEAR. All 668 new source lines are
read and pinned by the complete state review. The final pin verifier checks
157 whole files and 102 literal inclusive spans across six pin files. It retains
final newlines. Earlier planning pins and source cuts remain as marked history.
All heavy jobs run serially under verified 4 GiB max/high limits and zero swap.

## Next work and scope

1. Carry Related through the native cached enumeration state. Keep expandable
   and waiting indexes, edgesOf and constrainedRecursion configuration explicit.
   Preserve Caller, heap, memo and query endpoints through evaluated alternatives.
2. Derive and retain concrete stored-address and allocation-domain bounds from
   initialization and actual bounded operations. Related and root validity alone
   do not establish those bounds or Safe. Preserve canonical trie facts separately.
3. Preserve terminal-prefix order: record all original representatives, perform
   unions, read the final winner, move waiting counts for distinct recorded roots,
   assimilate the original raw slots, then merge the incoming node. Do not replace
   recorded sources by their post-union representatives.
4. Retain Canonical through actual recursive histories and derive semantic Ranges
   from genuine resource receipts. Cover partial stops and recursive truncation.
5. Prove whole recursive emitted-term soundness, discharge and rendering existence,
   selector coverage and forward completeness. The local captured renderer proof
   and the core correspondence do not establish these results by themselves.
6. Keep physical containers, machine Int bounds, concrete guard solvers, full
   typing/pruning and the new EGraph/cost-order APIs as explicit remaining scope.

Evidence: lean/restart-evidence/20261027-flat-enumeration.
All original strict attempts, source plans, reviews, native receipts and public
readbacks remain. Raw logs and raw patches use lossless gzip where needed.
The manifest records all payload byte counts and SHA256 values.
''')
print('Updated eight restart/index documents and wrote the focused core note.')
