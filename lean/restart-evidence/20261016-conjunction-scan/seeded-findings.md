# Current conjunction Scan: seeded-query findings

Date: 2026-10-16 06:58 CEST.

## Source shape

`Equality/Operations.hs` lines 219-230 use the secondary gate, project each
original class path, and call `intersectList`. Empty input is EmptyNode.
For nonempty input `n : ns`, the source uses `foldr intersect n ns`.
The new graph therefore rotates the first source operand to the final seed.
It has no `mergeAlternatives` operation in this refused-class query.

The old SourceEmptinessClassFold/SourceCurrentSeededQueryCompletion execution
uses the previous native interpreter. Its projection support remains useful,
but it is not a proof of checked-allocation query execution. The new graph
uses actual SourceEqualityNativeDemand traces and current operation states.

## Physical completion is derived

The false secondary gate derives anchored support for each proper selected
path. SourceCurrentAllocatedGateFields.forest_complete derives each finite
projection, CostHeap, SemanticReady, available closed result, and loaded
fields in the same operation cache. advancePhysical retains both native
memo tables and the domain cache.

For a closed available current value, closed_original derives Original from
current Good.native.machine.1.coherent. The result can be a newly projected
node or a generated intersection accumulator. Original here is a syntactic
property. It is not membership in a fixed original source inventory.

At each reached heap, ScopeCompletion.initial_complete uses those derived
original operands and the actual WordRanges to construct the finite checked
request. The scope invariant is independent of an input language model.
TraceEffects derives final Good, physical Effects, and machine Extension
from the actual trace and initial invariants. Native operations can grow the
actual equality cache. They retain the native caches across later requests.
The finite endpoint does not clear tables or replay an old interpreter.

Existing raw graphs have one result and one complete final state. Forest
uniqueness and checked done_stable prove that property. Seeded.effects aligns
the raw graph with the independently derived completion, including its
scope and closedness facts.

## Exact query semantics remains separate

WarmQuery.query_complete uses one fixed source view, finite input model,
rank model, and Contextual warm-cache invariant. Projected and generated
identities need not lie in that fixed finite model domain. Rebuilding a
fresh two-root model at each step does not transport the semantic laws of
already returned warm cells. Syntactic Original does not discharge this
model-validity obligation.

A sufficient next component is a model-extension theorem. It must add the
reachable domain of each new closed operand, retain the physical input
interpretation on all prior request operands, and transport both sound and
rank-bounded complete laws of returned cells. The transport must account for
the new source heap and ranked model. It must follow from retained physical
rows and independent least-language laws. It must not assume the desired
parent result law. A weaker alternative is an actual-history semantic cache
invariant with a proved admission rule for each newly generated operand.

Until that component exists, the new finite seeded theorem supports a
physical current conjunction Scan. A true emptiness answer is sound for the
constructed query, but exclusion of every class-satisfying original witness
also needs independently derived query inclusion. General current-source
class Scan semantics and full constrained reduction remain open at that
boundary. The graph also leaves source-runtime initialization, machine-key
identity, lazy evaluation order, and external solver behavior explicit.

## Reviewed source hashes

```
55e0434ab1dd7d232ad4546cd22aa5d8caa5dd91ef9651d7e7f5db4c8fb807bc  lean/MicroCFTA/SourceCurrentAllocatedSeededQuery.lean
6e2fa64de724b6e153b2744f2b2c9ecccb68f7a077143490c8f67a7e47e218ac  lean/MicroCFTA/SourceCurrentAllocatedGateFields.lean
d3ee51746d0affdfb623db252c6277409bf0167a0848679425281d59f5d6d2e8  lean/MicroCFTA/SourceCurrentAllocatedNativeScopeCompletion.lean
4168b87e3db60925ea6ccb04ab0068939ed72b53634d0757b79e5fc13cfd35df  lean/MicroCFTA/SourceCurrentAllocatedNativeTraceEffects.lean
5bf6e9b0f4033c11ac7723a17fe8d1b94d95a259187f0402285ad0147e439b09  cfta/src/Data/CFTA/Equality/Operations.hs
```
