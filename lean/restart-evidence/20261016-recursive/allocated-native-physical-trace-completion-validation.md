# Actual checked physical completion

Frozen and validated: 2026-10-16 05:40 CEST.
Source: `lean/MicroCFTA/SourceCurrentAllocatedNativePhysicalTraceCompletion.lean` (559 lines).
SHA256: `eb9dcb6701c7742118b227da9d6322a6e9170eb6fa989c3db6369a99b2064008`.
The prior CodeProgress, PhysicalExecution, and PhysicalCompletion files remain unchanged.

## Result

The paired actual physical completion induction is closed. No smaller-body completion callback, own-body done equation, future physical input plan, future cache validity, NodeProduced, EdgeProduced, or desired result-language law is a public completion premise.

Namespace: `MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion`.

- `Trace` records the actual checked yielded controls, whole states, and each current PhysicalExecution.Inputs check. `Trace.steps` erases only the physical-check proofs. `Trace.trans` and `Trace.bind` preserve exact control and full-state continuity. `Trace.plan` derives InputsThrough at fuel+1 from a constructed pure-return trace.
- `Receipt` contains that trace, Good at its actual returned state, machine Extension, heap Keeps, operation-cache Grows, and the chosen structural postcondition. `Receipt.done` derives the literal NativeDemand.execute completion equation.
- `code_complete` derives Returned from structural Safe, Operands, Below, initial Good and CodeFields, original source growth/history, ActiveAbove, and actual WordRanges.
- `node_complete` and `edge_complete` derive actual body returns at the independent schedule bound. The latter runs actual edgeBody, including mismatch, rejection, and allocated accepted-child code. It does not run old eager compileEdge.
- `request_complete` also includes actual lookup, publication, and demand.
- `initial_complete` derives the independent schedule Completes and structural certificates from closed available Original inputs. Idle supplies every initial active bound. Its only remaining runtime-plan premise is WordRanges on actual checked prefixes. It returns a Receipt and final Idle.

The private all_bodies proof uses strong induction on independent requiredFuel. Both node and edge callback fields are discharged internally from a strictly smaller bound. The structural code induction invokes those certified smaller requests. It does not assume an equal old eager execution or old Produced validity.

## Actual frame handling

Physical cache Shape excludes absent published handles. Exact physical captured-request identity and strict ActiveAbove bounds exclude busy demand. Returned hits recover resident values without replaying their bodies.

A started request constructs its actual body trace. The existing checked Running theorem derives that the original evaluating cell survives that same trace. Its actual physical finish stores only the derived Available or EdgeResident result. The same trace restores the caller's enclosing active bound. Trace.bind appends that exact finish frame and composes the continuation at the exact returned whole state.

Actual primitive work and optionalBinder effects use initial ready heaps and physical arguments. The optional-binder completion theorem excludes pending construction from these initial conditions. Equality fields come from the same actual allocation prefix and remain in the literal returned operation cache. The guard equality instance remains pinned to the source guard equality.

## Initial premises and limits

`Good` contains initial physical cache Valid, RequiredCache.Ready, equality-operation Valid, and successful same-cache equality Fields. `initial_complete` additionally needs initial Idle, closed available Original operands, and WordRanges for the actual request. It derives schedule completion and the reached physical checks; these are not supplied as whole-run completion oracles.

WordRanges is still an explicit machine-word contract over reached actual yielded prefixes. This proof does not establish that every mathematical identity fits a fixed width. It also does not derive initial loaded sidecar fields from arbitrary Haskell construction or replace a missing-cache state with a successful one.

The result is physical: actual completion, cache validity, field availability, residency, heap/domain/operation growth, and final idle state. It does not establish the returned language or final result closedness. A physically resident warm result may still need an independent contextual cache language invariant. The semantic paired induction, current top-level query/caller composition, GHC demand scheduling, publication/concurrency, and runtime-container correspondence remain separate obligations.

## Validation

Focused command:

`/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion`

Result: terminal exit 0, 1087 jobs. No new warnings. The pre-existing unused-input warning at InternedFreshOrdinaryClosedCompletion:24 was replayed.

Probe command:

`/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-recursive/allocated-native-physical-trace-completion-probe.lean`

Result: terminal exit 0. Ten public theorem axiom checks use only propext, Classical.choice, and Quot.sound. Four kernel examples verify:

1. One actual receipt supplies both execute.done and its reached physical input plan.
2. Closed original roots derive raw actual completion, all physical effects, final residency and Idle, and stable completed execution under extra fuel.
3. Actual checked edgeBody derives a resident completed row from the initial invariant and independent request bound.
4. The constructed physical plan transfers initial SemanticReady and stored CostHeap to the same actual returned heap through existing effect theorems.

Independent read-only review by guard_inventory found no material defect in the final frozen strong induction. The probe's first run used a nonexistent CostHeap type alias; the corrected evidence uses the actual InternedFreshOrdinaryCostHeap.Heap. No proof-source correction was needed.

No older Lean source, Audit, documentation, Haskell, or Git state was edited by this work.
