# Finite exact partial reduction of equality-free original syntax

Proofs: `ee4cd6da` and `347a988f`.
Source: `TharkunAB/cfta`, `origin/main` at `33148e6d`.
Integration: `af4a2b87`. Continue on `formalize` and push checkpoints.
Read [the recursive memo proof](notes-recursive-memos.md) and
[the Sized comparison](notes-canonical-upstream.md).

## Current upstream and preservation

Upstream now contains the retained-cycle traversal repair in `c292354b`.
The current Equality.Operations, Interned.Operations, Template, and
EqualitySpec files are byte-identical to main. The merge changes none of
these local bytes. The local fresh-probe changelog note remains present.
The only merge conflict was duplicate changelog context. Both repair notes
are retained. Backup:
`backup/formalize-before-retained-main-20261015-0925`.

Hoogle+ data moves to the public `cfta-generator:hoogleplus` sublibrary.
The affected GHC benchmark now depends on that library. Upstream also adds
the cfta-ghc package metadata check to CI. Sized and all existing proof
definitions remain unchanged by this refresh.

The first combined test command passed core tests, then failed because
the new Hoogle+ installed unit was absent when Cabal built refinement tests.
Building the public sublibrary first resolved that failure. The subsequent
run passes all 650 examples: 293 core, 210 generator, and 147 refinement.
The affected cfta-ghc hectare-ghc benchmark compiles. It was not run.
Fourmolu, all three active Cabal formatting checks, and all three package
metadata checks pass. No local production test or build workaround is added.
Logs: `/tmp/mcfta-retained-main-20261015-{tests,staged-tests,format,metadata}.log`.
Preservation record: `/tmp/mcfta-retained-main-refresh-preservation.json`.

## Actual finite caller regions

SourceEqualityPartialPlainRegion follows the actual source traversal.
Region stops at EmptyNode, Mu, and interned union branches. Ordinary nodes
retain every row. Each row reads the actual empty physical equality payload
and has structural child regions. There is no successful bare Rec case.
Mu and union bodies can contain equality constraints below their opaque
caller boundary. Full edge guards remain present.

SourceEqualityPartialPlainPrefix executes the literal empty precheck and
edge request. It proves original ordered child readback, actual empty
payload combination, and empty descent at every child index. The unchanged
precheck reaches no primitive native word request. No range hypothesis is
needed for these local prefixes.

SourceEqualityPartialPlainCompletionCases derives actual finite binder,
ordinary row, child, and tail branches at their real warm states. Mu uses
both fixed probes and the resident canonical hit. Each empty native prefix
retains the original structural child list. Completed smaller child effects
derive the next physical scope and histories. Literal edge construction
then supplies the real tail state. No future scope or complete recursive
graph is supplied.

SourceEqualityPartialPlainCompletion.complete performs the mutual structural
induction. Every closed available Region has a completed actual outer graph.
This proof does not use cached input depth. It uses smaller original
ordinary child regions and actual opaque source branches.

## Original source syntax and exact finite public execution

SourceEqualityPartialPlainAnnotations.NoEqualities is the actual source
guard accessor returning the empty equality set. Physical annotation heaps
derive Region for every closed available annotated value. Original source
construction supplies that heap from its literal guard checks. The proof
also covers discarded alternatives and binder probes.

SourceEqualityPartialPlainSource.region_exact derives finite complete public
execution from Region and its actual initial physical scope. closed starts
with original normalized closed syntax whose guards have empty equality
readback. It constructs the initial value and heap, derives Region, and
constructs the completed recursive graph. The result has both actual source
gate memo receipts, native readiness, normalized annotations, both filtered
probes, retained histories, and closed available output. Its public language
is the original expression's independent guarded least language.

NodeRun supplies a common sufficient bound for traversal and all six native
stages. Every larger seven-bound execution returns the identical physical
value and full native state. No successful bounded receipt, completed outer
graph, caller termination law, native word-range hypothesis, or sufficient
bound is an input premise. Residual guards stay intact; equality freedom
does not require an unconstrained full guard.

## Validation and remaining scope

All six new modules pass focused builds. The aggregate audit passes 1,863
jobs and 48,189 dependency checks with only propext, Classical.choice, and
Quot.sound. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-plain-completion-20261015-audit.log`.
All older proof bytes except audit imports, counterexamples, marked drafts,
stashes, and other worktrees remain unchanged. All traversal repair bytes
and regression bytes are unchanged by the upstream merge.

Next extend equality-free region completion to arbitrary inherited payloads.
Retain actual contradiction and empty selected-class branches, concrete
prechecks, physical combination and descent, and final empty propagation.
Derive local finite execution and returned scope before structural recursion.
Then study general selected narrowing with a valid measure or a focused
counterexample. Native intersection can increase ordinary depth.

General constrained outer success, the outer reduction memo table, open
contexts, repeated fixed points, getAllAtPath, native containers, GHC lazy
scheduling, and extraction remain separate. This theorem does not prove
them. Preserve Sized exact classes, finite size execution, size order,
both distinct rank inverses, and the optimized interned core.
