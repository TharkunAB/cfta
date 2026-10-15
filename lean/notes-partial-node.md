# Actual outer partial-reduction step

Mutually recursive completed outer graphs now derive scope and public language
without a supplied Callback law. They preserve both physical heaps. Arity,
changing-callback replay, complete physical determinism, and original closed
source entry are checked. The next target is the reverse bounded-worker graph
proof with actual reached word checks. General caller termination remains open.
Read [the current note](notes-recursive-graphs.md). This paragraph supersedes
older graph and replay targets in this note.

Both filtered Mu probes now have an explicit physical heap invariant. Actual
source and native execution, reads, merging, targets, shared edits, and complete
guarded passes preserve it. The returned heap supplies exact outer Mu execution.
Next use mutually recursive completed outer graphs to obtain actual child
induction hypotheses, then prove bounded worker agreement and replay. Carry
the probe invariant explicitly; current IdleReady does not contain it. Read
[the current note](notes-filtered-probes.md). This paragraph supersedes older
probe propagation and unrestricted callback targets in this note.

Updated: 2026-10-15 08:19 CEST.
Proofs: `6aa6c341`, `94860ace`, and `1ec8eb87`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
The retained traversal repair is `61f2c939`. Continue on `formalize`.

## Cached Mu reconstruction

InternedFreshOrdinaryProbeFilter.filter_fixed proves the complete physical
identity of the source filter on a root with no matching bare union member.
The result retains both the complete probe record and the exact input heap.
callback_clean follows the actual repaired body execution and its final filter.
It derives the filtered-root property from the retained semantic source context.
origin_clean uses the actual original Depth and selected ordinary probe calls.
resident_clean and constructed derive both obligations for actual stored Mu
records. They do not assume a semantic binder preservation law.

SourceEqualityMuReconstruction.matched uses the existing probeReadback fast
paths and the actual repaired stored substitution fallback. The source tests
the ordinary argument before Depth. The existing helper tests Depth first.
These two Reference constructors are disjoint, so the fast paths agree.
callback applies the actual withoutSelfReference operation after matching.
rebuild performs both probes, chooses the ordinary argument from the returned
Depth probe, requests the physical Mu key, and selects smart finish.

depth_call and ordinary_call derive unchanged physical probe calls.
resident_hit derives the complete canonical table hit from coherent residency.
It permits arbitrary fresh-body code because that code is not executed on a
hit. completed and from_origins return actual smart cleanup at the identical
heap. verified proves availability, exact free-name metadata, and exact guarded
language for that result. Raw redundant binders can change their physical node.
The proof therefore does not replace this source branch by node identity.

SourceEqualityPartialStepProofs.constructed_mu starts with an actual original
closed construction and a complete stored Mu record. The source cache derives
availability and both probe premises. Every positive traversal bound executes
that exact Mu branch with identical full native state and exact guarded meaning.
This theorem does not require a supplied callback law or word-range premise.

## Ordered native rows

SourceEqualityInheritedRows.walk runs the concrete local native edge pass and
its inherited continuation before the next row. It retains each actual returned
warm state. The first error or incomplete edge observation stops the row walk.
No tail request runs after that observation.

Graph records individual concrete source edge executions at their actual scopes.
Graph.length preserves row count. Graph.stable combines each row's six native
stage bounds with componentwise maxima. Every sufficient bound returns the same
ordered rows and full native state for that fixed recursive node callback.
Ranges applies native word checks only at actual reached row prefixes.
graph derives concrete edge receipts from a successful worker and those checks.
This is not a claim that an arbitrary row graph completes with an arbitrary
recursive callback or that increasing traversal fuel preserves that callback.

SourceEqualityInheritedRowsProofs.edge_verified composes the actual native
guarded pass and inherited child graph. graph_verified performs the pointwise
row induction. It advances earlier edge residency through actual cache growth.
It derives idle validity, histories, complete row residency, closed children,
physical annotations, unconditional narrowing, and exact public row-union
meaning when the inherited equalities hold. The smaller recursive node law
remains the explicit Callback premise from the child proof.

## Actual node construction and outer branches

SourceEqualityPartialNodeRebuild.modify follows source modifyNode. It compares
ordered interned edge identities before construction. Equal identities return
the original node and native state. verified uses coherent resident edge records
to derive equality of the complete ordered rows on that branch. Changed rows
use literal makeNode and advance the same native state. Both branches derive
availability, closure, annotations, histories, and exact row-union meaning.

SourceEqualityPartialWorker.step retains EmptyNode, the source Rec error,
identical interned-union return, actual Mu reconstruction, ordered native rows,
and literal modifyNode reconstruction. Observation keeps actual unfinished rows,
pending constructor keys and native states, or traversal exhaustion at its
exact input. run decreases the traversal bound only at recursive node entries.
Its zero bound is incomplete. The six native bounds are separate parameters.
This adapter unfolds source go. It does not model genericReducePartiallyCache
or prove correspondence with GHC lazy forcing and retention.

SourceEqualityPartialStepProofs.closed_rows derives actual child closure from
coherent free-name metadata. ordinary composes the concrete row graph with both
literal node branches. Checks retains filtered probes on Mu and reached native
word checks on ordinary nodes. step_verified proves the full local Callback
conclusion for every successful step under these checks and the smaller-call
premise. Errors and incomplete worker observations do not count as completion.

## Next proof obligations

Derive a physical heap invariant for both filtered probes in every complete Mu.
Original source origins establish it, but current IdleReady does not contain
it. Prove preservation through actual source construction, stored substitution,
optional binders, native compilation and evaluation, exposure, merging, shared
edits, folds, and edge reconstruction. Carry that invariant explicitly. Do not
infer it from semantic probe-language heaps; they do not state root filtering.

Then derive the recursive node Callback by traversal-bound induction with the
actual reached word checks. Existing child and row proofs keep Callback
explicit. The successful-step theorem does not discharge recursive calls by
itself. Prove replay across larger traversal bounds when recursive callbacks
change. Fixed-callback six-stage stability does not establish that property.

General caller termination remains unproved. Actual native intersections can
increase ordinary depth, so cached original depth is not a termination measure.
The outer memo table, open contexts, repeated fixed points, getAllAtPath, native
containers, GHC lazy scheduling, and extraction remain separate obligations.
Sized exact classes, finite size execution, size order, and both distinct-term
rank inverses remain checked at their documented source boundaries.

## Validation and preservation

The focused builds and aggregate audit pass. The audit runs 1,819 jobs and
47,971 dependency checks. Only propext, Classical.choice, and Quot.sound are
permitted. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-partial-node-20261015-audit.log`.

Seven proof modules are new. Older proof bytes change only in audit imports.
All counterexamples and marked drafts remain. Production Haskell is unchanged.
The earlier 645 Haskell examples and formatter checks were not rerun.
No board posts, deployments, or external messages were sent.
