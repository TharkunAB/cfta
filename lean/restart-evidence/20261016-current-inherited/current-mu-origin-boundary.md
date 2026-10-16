# Current Mu reconstruction and filtered-probe boundary

Reviewed and implemented at 2026-10-16 10:17 CEST. No older proof source,
Haskell, Audit, documentation, or Git state was changed.

## Current readiness does not contain the needed receipt

`SourceCurrentConjunctionClassScan.Ready` stores Good, SemanticReady,
CostHeap, scoped native cells, and native Idle. Its SemanticReady stores
required-cache Ready plus guarded and budget probe-language heaps.
Required-cache Ready stores SemanticHeap, Covered [], and open depth
readback. SemanticHeap stores Context [] and the decoded depth heap.
Context stores Normal, available lexical inputs, decoded profiles, and
decoded free names. Normal stores physical facts, live edges, flat unions,
nonempty records, and nonempty union members.

Neither this chain nor InventoryState.At stores the two physical probe
filters. At stores input-model Contextual, request admission, source heap
growth, and issued history. Available stores residency, issued names, and
recursive child availability. No existing derivation from their conjunction
to filtered probes was found. This review does NOT prove that every
unqualified Ready-to-filter implication is false. It does not invent an
unchecked counterexample and call it a Ready heap.

The exact required property is
`InternedFreshOrdinaryProbeFilter.Clean depth ordinary`. This means
`InternedStoredSelfFilter.NoSelf .depth depth` and
`NoSelf (.uninterned (ordinaryLevel depth)) ordinary`. NoSelf excludes the
specified bare reference as a direct root-union member. It does not exclude
bound references below ordinary constructors. This pair property differs
from the separate `InternedStoredSelfFilter.Clean state` body invariant.

`InternedFreshOrdinarySemanticOrigins.Heap` is sufficient through
`ProbeFilter.resident_clean`, but contains more historical information than
needed. The smaller existing `InternedFreshOrdinaryProbeHeap.Heap` states
that every stored Mu retains this Clean pair. Its `resident` theorem
derives the exact pair from actual Available residency.

## Actual available construction laws

`ProbeHeap.closed_heap` derives the invariant from an actual closed
`InternedFreshOrdinaryConstruction.build`. `ProbeHeap.build_heap` retains
it at every done or pending outcome from an actual Context and initial
ProbeHeap. New stored Mu records receive the actual `callback_clean`
proofs before completion. This is source construction evidence, not a
supplied desired rebuilt result.

`ProbeHeap.node`, `.union`, `.edge`, and `.filter` preserve the invariant
through those actual work operations. General `preserve` needs the actual
NoNewMu relation. `SourceEqualityProbeUnfold.execute` and `.unfold` retain
the invariant through actual fresh stored execution with available
replacements; they allow open stored values. Older ProbeExposure/Pass
theorems use historical graphs and whole-closed inputs. They cannot serve
as current execution transfer endpoints without a new actual graph proof.

New `SourceCurrentAllocatedMuRebuild.lean` supplies the current checked
primitive bridge. Its `optionalBinder_heap` rewrites the actual maybeMu
operation using `SourceRecursiveIntersectionMaybeMu.maybeMu_eq`, then
applies actual `ProbeHeap.build_heap` to the literal compiled stored-body
plan and current available leaves. The unused-pair branch is unchanged.
It assumes initial SemanticReady, initial ProbeHeap, and actual body
availability. It assumes neither a prepared/final body nor a result law.

`work_heap` handles precisely the actual WorkInputs constructors: pure,
edge, ordinary node, and union. It makes no claim for arbitrary Work.
`step_heap` follows all actual checked instructions. Read, enter,
finish, node/edge publication, and edgeBody retain the constructor heap.
Ordinary work and optional binders use the preceding actual laws.
`execute_heap` follows only yielded steps and derives intermediate
SemanticReady from actual current physical checks. It retains the exact
heap on successful, failed, constraint-error, blocked, and exhausted
finite observations. It does not replace checked execution by an old
native execution.

`execute_heap_of_physical` uses the existing reached physical-plan
projection. `trace_heap` gets that plan from the actual physical Trace and
uses execute(fuel+1) at its actual done state. No final ProbeHeap,
semantic result, future invariant, or callback success is a premise.

## Resident rebuild endpoint

`resident_rebuild before ready probes entry body depth ordinary available`
derives

```
MuReconstruction.rebuild entry body depth ordinary before.heap =
  done (cleanup (mu entry body depth ordinary)) before.heap
```

It also returns Available cleanup, equality of free lists, and exact
independent meaning for every guard interpretation and ambient environment.
It derives Clean through `ProbeHeap.resident`, coherence through current
Ready, and uses the actual depth/ordinary callback and canonical-hit proof
in `SourceEqualityMuReconstruction.completed`. No original-source origin
history, whole-value closedness, or desired rebuild equation is supplied.

`actual_rebuild` aligns any actual raw binder branch's completed result
with this cleanup and the SAME heap. A checked-state advancement at that
heap and same operations is the same checked state. The external kernel
`kernel_current_binder` proves that an actual current PartialGraph.NodeBody
Mu branch returns cleanup and retains the WHOLE Caller state, including
both outer result tables, full checked/native/equality state, merge memo,
and fourth memo. This is a direct integration, not a source change.

## Remaining composition

ProbeHeap remains an explicit additional representation input at current
warm entry. Original construction discharges it. To remove it from a
constructed whole-caller endpoint, thread it through the actual current
gate/head/projection/merge/checked query/conjunction worklist/required/edit/
class/local-parent graphs, then the mutual outer caller graph.

Heap Keeps or physical Effects alone is not a proof of this transport:
they retain old records but may add new Mu records. New records need the
actual constructor proof above. Completed global-memo hits need their
same exact operational graph and heap receipt. Do not assert generic
Effects-to-ProbeHeap or import historical ProbePass as current execution.
No general recursive outer termination or GHC demand/publication theorem
is supplied by the new invariant.

## Current PartialGraph source review

Reviewed `SourceCurrentAllocatedPartialGraph.lean`, SHA256
`df184b5a142d999896ba93efb75d354a7dc5d94237b6daf162e62d42d917091c`.
No material raw-graph defect was found.

The binder branch records the literal actual MuReconstruction return. This
is correct for `Equality/Operations.hs:85`: the Mu pattern is a view pattern
whose constructor is createMu (`Interned/Type.hs:629–676`). It reconstructs
through both filtered cached probes and smart cleanup. The result is not
unconditionally the original Mu: createMuDontCleanup can retain a binder
that smart cleanup removes. The graph therefore correctly avoids an
unproved identity or unchanged-heap assertion.

Empty and interned-union branches retain the original values. Ordinary
rows run edge request, returned-edge descendants, then tail in order.
Inherited combination occurs once; per-child descent uses its actual
returned allocated value and indexed original child. The edge body records
the current ParentEdge and requires the original field load only if raw
contradiction is false. Contradiction skips child calls. A raw Rec has no
successful NodeBody constructor, matching the source error. Same-arity raw
edge rebuild and literal modifyNode are retained.

This graph describes completed serial calls, not completion for all
inputs. Busy/absent observations have no successful constructor. Arbitrary
raw warm cells need their later physical/key/semantic invariants before
preservation can be claimed. The separate three-global-table Reads graph
and GHC first-writer/lazy publication transfer remain distinct obligations.
