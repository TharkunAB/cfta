# Filtered Mu probes through actual equality execution

Updated: 2026-10-15 08:33 CEST.
Proofs: `a93cc716`, `e5aaebde`, and `e1916030`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
The retained traversal repair is `61f2c939`. Continue on `formalize`.

## Physical invariant and source construction

InternedFreshOrdinaryProbeHeap.Heap states that each complete Mu retains both
actual filtered probes. Its Depth probe has no bare Depth reference as a root
union alternative. Its ordinary probe has no bare selected ordinary reference
as a root union alternative. The selected ordinary argument is computed from
that stored Depth probe. This is a physical record property. The existing
independent probe-language heaps do not state it.

build_heap, buildMany_heap, and buildEdges_heap follow actual repaired source
execution at every complete or pending outcome. Old records need only the
probe invariant. They do not need a retained original-call history. New complete
records use callback_clean at the actual original probe calls. The proof retains
both probe stages, actual fresh reservation, the callback body, and first-writer
readback. closed_heap derives the initial invariant from the empty source cache.
resident exposes both fixed filters at a real available Mu. Ordinary node,
union, bare-self filtering, and edge construction preserve the same invariant.

## Source effects and native execution

SourceEqualityProbeUnfold.execute preserves the invariant through actual repaired
stored substitution. Available original and replacement values derive the source
context. unfold uses its original Mu as the sole replacement. Both the complete
and pending outcomes retain the invariant.

SourceRecursiveIntersectionProbeEffects.optionalBinder follows actual stored-body
compilation and repaired source execution. The unused branch has no constructor
effect. The used branch retains filtered probes through both probes, reservation,
and its source body.

SourceRecursiveIntersectionNativeProbeHeap.Bounds.filtered_probe_heaps follows
actual bounded native evaluation. It retains semantic heaps and filtered probes
through ordinary jobs, domain effects, direct calls, memo hits, started node and
edge bodies, optional binders, completion frames, and continuations. The existing
OrdinaryWork proof derives that ordinary compiled jobs introduce no Mu. Explicit
optional binders use their actual source preservation theorem. No final heap
property or arbitrary work-preservation law is supplied.

SourceEqualityNativeProbeScoped.step specializes that proof to the actual
word-checked scoped native intersection request. The returned warm state retains
the invariant. It does not reset either native memo family.

## Reads, merging, and the complete guarded pass

SourceEqualityProbeExposure retains the invariant through every bounded cold
worklist and direct nodeEdges read, including exhaustion. SourceEqualityProbeHead
adds actual row-node reconstruction. SourceEqualityProbeRequired follows the
mutual node, child, and row graph. SourceEqualityProbeProjection follows general
path projection, ordered operand reads, and the final source node construction.
No operation assumes its future output invariant.

SourceMergedProbeComparison retains real allocating comparison effects and all
intermediate scopes. SourceMergedProbeSelection covers recursive cover scans,
retention, and identity filtering. SourceMergedProbeWorker follows ordered
recursive calls, retained unions, the recursive-boundary branch, ordinary unions,
the four-row threshold, original small-row guards, and literal large-row Top.
Its ordinary-fuel induction derives complete general merge preservation from
the actual worker. No complete merger preservation law is supplied.

SourceEqualityProbeTarget composes actual captured-forest projection, merging,
the first-seeded native right fold, target construction, first forcing, reuse,
and subsequent shared native leaves. SourceEqualityProbeSharedEdit follows the
mutual shared edit graph and actual original capture scope. SourceEqualityProbePass
retains the invariant through fresh class captures, tail-first class folds,
single final empty propagation, closed gate selection, actual required paths,
selected folds, checked one-pass branches, and literal guarded-edge allocation.

SourceEqualityPartialProbeEntry.constructed derives the initial probe heap from
an actual completed original closed construction. guarded_mu connects the
complete concrete native pass to outer reconstruction. Every available Mu in
the actual returned heap has both fixed filters. Every positive outer traversal
bound therefore returns smart cleanup with the identical full native state and
exact independent guarded meaning. No generic binder language law is supplied.

## Next caller proof

The current IdleReady type remains unchanged. It does not imply this physical
probe invariant. Carry the invariant with each actual recursive scope.
The earlier successful-step theorem also retains a global Callback premise.
That premise quantifies all IdleReady scopes. Do not assume it for the recursive
worker merely because the new native probe theorem is available.

Assemble mutually recursive completed graphs for outer nodes, ordered rows, and
indexed inherited children. Retain the actual checked local native prefix,
physical payload readback and combination, child indexes, Mu request receipts,
and modifyNode fast path. Graph induction can then supply each actual recursive
child law while preserving both physical heaps and public language.

Prove bounded worker agreement by traversal-bound induction with actual reached
word checks. Prove replay across larger traversal and native stage bounds.
The recursive callback changes when traversal fuel changes, so fixed-callback
row stability alone does not supply replay. Preserve every error and incomplete
observation. General finite execution for the full caller remains unproved.
Native intersection can increase ordinary depth. Original cached depth is not
a termination measure. The outer Haskell memo table, open contexts, repeated
fixed points, getAllAtPath, native containers, GHC lazy scheduling, and extraction
remain separate obligations.

## Validation and preservation

Sixteen new proof modules pass focused builds. The aggregate audit passes
1,835 jobs and 48,053 dependency checks. The permitted foundations are propext,
Classical.choice, and Quot.sound. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-filtered-probes-20261015-audit.log`.

Older proof bytes change only in audit imports. All counterexamples and marked
drafts remain. Production Haskell is unchanged. The earlier 645 examples and
formatter checks were not rerun. Sized exact classes, finite size execution,
size order, and both distinct-term rank inverses retain their existing proofs
and documented source boundaries. The optimized interned core remains.
No board posts, deployments, or external messages were sent.
