# Concrete PCS guard laws and normalized source annotations

Updated: 2026-10-15 07:17 CEST.
Proofs: `8fe4544e`, `50bdc097`, and `307f83be`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
The retained traversal repair is `61f2c939`. Continue on `formalize`.

The native-output annotation target below is now proved for the actual scoped
native intersection. Repaired unfolding, bounded exposure, complete required
paths, and general projection also retain annotations. The complete equality
pass still needs general merging, shared-target edits, gate queries, and fold
preservation. Read [the current note](notes-native-annotations.md).

## The independent constraint meaning

EqualityNormalize already defines PCS classes by equality of distinct paths.
Empty and singleton classes impose no condition. SourceEqualityPCSGuard uses
that existing meaning for stored equalities and retains the actual complete
public source guard decision. It does not alter a source worker or accessor.

normalize_sat and combine_sat prove that actual source normalization and
combination preserve this meaning for arbitrary raw lists. public_eq proves
agreement with acceptsConstraint on active stored source classes. The previous
singleton_storage_boundary remains unchanged: a malformed singleton can make
the public existence test stricter than the raw PCS meaning. Such storage is
outside the documented source representation invariant.

positive_sat derives complete staged positiveEqualities meaning. positive_source
includes actual sourceEqualities empty and combination branches. own_sat handles
positive and residual source guards. It supplies physical own satisfaction
without assuming a guard-to-payload law.

## Concrete native edge controls

SourceEqualityPCSConstructors proves global Top, plain, and conjunction laws
at independent PCS semantics. The earlier normalized public constructor laws
remain valid. They are not silently generalized to malformed raw payloads.

SourceEqualityPCSGuardedEdge retains literal guarded reconstruction and gives
independent PCS output inclusion and exactness under inherited satisfaction.
Own physical validity and satisfaction come from actual accessor readback.

SourceEqualityPCSNativeEdge fixes every source control. guardDecidableEq uses
the existing actual structural comparison and its equality theorem. conjoin
uses source guard order. The empty-edge constraint and merged-target guard
are the literal noConstraint Top payload. The node predicate is the actual
source memo gate; clear is actual SourceMemoGate.plain.

The language theorem discharges every generic constructor law with the proved
PCS source law. source_edges derives finite complete execution from original
closed construction, both source memo certificates, literal full labels, stable
six-bound worker results, and exact independent PCS language under inherited
satisfaction. No generic clear/top/conjunction language contract is supplied.
Only reached primitive native word checks and source representation remain.

## Stored-record annotation readback

SourceEqualityAnnotationLanguage.Annotated checks complete edge guards in
semantic stored bodies. It omits probe metadata because the independent
language does not read that metadata. meaning_congr_holds transports complete
stored language when the two guard interpretations agree on these annotations.
The proof includes ordinary nodes, ordered forests, unions, and least-language
Mu binders with the same actual reference environment.

public_eq and edge_public_eq apply the actual source payload invariant. Every
annotated source value and edge has identical independent PCS and current
public indicator interpretations. This is a pointwise proof on stored records,
not an extraction or lazy demand claim.

## Actual physical annotation heaps

SourceEqualityAnnotationHeap.Heap checks guards on actual edgeRecords keys.
Available linked values derive every semantic annotation from this invariant.
Canonical edge hits retain those keys. SafeWork checks emitted edge guards and
all constructor continuations. Its run theorem preserves the physical heap.
makeEdge emits its literal guard. makeNode, makeUnion, and withoutSelfReference
emit no new edge guard. These facts follow their actual source constructor code.

SourceEqualityAnnotationConstruction.Allowed checks every original edge literal,
including children and binder probe bodies. build, buildMany, and buildEdges
retain Heap through original repaired source execution. The proof covers both
probes, fresh binder reservation, canonical hits, pending readbacks, and final
record installation. It does not assume a successful final heap. closed derives
finite original construction, the physical heap invariant, and all semantic
annotations from the original syntax checks.

SourceEqualityAnnotationStoredSyntax proves encodeMany and encodeEdges retain
ordered original source guards. encode_allowed includes closed captures and
open nested binders. optionalBinder uses the actual source compilation equation
and the construction theorem. It preserves Heap in complete and pending outcomes
without a supplied compiled-syntax annotation premise.

## Current public entry and exact remaining boundary

SourceEqualityNormalizedEntry starts from original syntax with normalized
stored annotations. It derives its own physical heap and public input readback.
The concrete finite native edge pass then has returned PCS meaning exactly
equal to the original public edge meaning in a satisfying inherited context.
Own edge validity is derived from actual resident records.

Public readback of newly constructed outputs is still open. Do not call the
current entry public/public exactness. Prove Heap through actual completed
native evaluation, required paths, projection/merge targets, and shared edits.
Then available returned children derive their annotations, and edge_public_eq
will transport the output to public meaning. No final output invariant should
be supplied to claim source correspondence.

A direct route is an annotation-specific continuation certificate alongside
SourceRecursiveIntersectionCode.Semantic. Follow Bounds.semantic_heap through
actual jobs, optional binders, ready memo hits, started bodies, and completion
frames. SafeWork and optionalBinder already supply local constructor rules.
Concrete conjoin_cached needs no input invariant for its newly normalized
output; Top is cached. Retain exact native cache scopes and reached ranges.

Then connect inherited descendant processing and the full reducePartially
traversal. Open contexts, repeated fixed points, getAllAtPath, native containers,
GHC lazy scheduling, and extraction remain separate. Preserve the optimized
interned core and the exact Sized contracts and both distinct-term inverses.

## Validation and preservation

All nine new modules pass focused Lean 4.34.1 builds. The aggregate audit passes
1,791 jobs and 47,684 theorem dependency checks. Only propext, Classical.choice,
and Quot.sound occur. Only the older unused inputs warning remains.
Log: /tmp/mcfta-normalized-annotations-20261015-audit.log.
Snapshot: /tmp/mcfta-normalized-annotations-checkpoint-20261015-0717/.
It retains 2,196 Lean-tree files and four root documents. Older proofs except
audit imports, all counterexamples, marked drafts, production source, stashes,
and other worktrees are unchanged. The earlier 645 Haskell examples and formatter
checks apply to the unchanged source and were not rerun.

Lava's explicit function and graph method still applies. Neither its call-by-value
theorem nor assumed termination discharges source representation, native heap
invariants, GHC demand, or extraction. No Lava or Rocq dependency is added.
