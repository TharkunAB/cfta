# Physical transitions and finite base completion

Frozen: 2026-10-16 05:24 CEST.
Source: `lean/MicroCFTA/SourceCurrentAllocatedNativePhysicalCompletion.lean` (331 lines).
SHA256: `ad0fa0abaa240d8bf981734abd0ab6ae66d500c439a76084f1cc5c16ade581d2`.
The prior PhysicalExecution and CodeProgress hashes remain unchanged.

## Result and scope

The new module proves necessary actual transitions for general checked completion. It also proves an actual finite fresh pure-body call. It does not prove general recursive completion.

Namespace: `MicroCFTA.SourceCurrentAllocatedNativePhysicalCompletion`.

`Good state` contains PhysicalCache.Valid, RequiredCache.Ready, equality-operation Valid, and successful same-cache equality Fields. It contains no language law, old eager provenance, or completed recursive execution.

- `step_fields` removes the old semantic native-validity dependency from allocated field preservation. It follows the actual checked step, including physical publication and demand. It retains successful field loads and the actual yielded continuation's CodeFields. Its explicit inputs are current physical checks and initial CodeFields.
- `step_invariants` derives Good, machine Extension, heap Keeps, operation-cache Grows, and OutcomeFields through every actual step outcome.
- `execute_invariants` derives those facts at every actual finite outcome from Good, initial continuation Fields, and the physical-only reached InputsThrough. It derives future fields; none is supplied. This is preservation with a reached physical plan, not a general termination theorem.
- `node_step_yields` and `edge_step_yields` prove the actual request step yields. Physical Shape excludes absent handles. Exact captured-request identity, ActiveAbove, and strict independent requiredFuel exclude busy demand. The returned whole state has Good and all histories, with actual continuation Fields. No completed recursive child is assumed.
- `body_prefix` derives the actual checked edgeBody prefix from Good, resident originals, source EdgeScope, and independent Completes. It returns actual allocated operation state, derived CodeFields, Safe, Operands, and strictly bounded child code. Mismatch and rejection keep the real sentinel branch. No synthetic eager child execution is introduced.
- `pure_miss_complete` constructs the literal lookup, fresh demand, own physical finish, and return for an actual source body equal to `.pure value`. It derives value availability from compileNode_safe and constructs the actual two-step trace, execute3 equation, all reached physical checks, and final Good. It takes no own-body done equation or semantic result receipt. The proof covers the literal pure source branches; the probes instantiate actual self and empty-first guards.

The captured original record and both memo families remain in the actual native state. The operation cache is the literal returned cache. The guard equality instance is pinned to SourceEqualityPCSNativeEdge.guardDecidableEq where the source operational terms require it.

## Exact remaining general induction

No new mathematical counterexample was found for the intended original-input domain. The remaining proof is the joint structural and strong-requiredFuel induction, not an additional semantic result assumption.

A useful remaining invariant is an actual yielded trace with physical Inputs at each current control, paired with its original body postcondition and its protected running finish frame. The inductive result must construct that trace, result availability, Good, Extension, Keeps, and operation Grows together. A bind lemma must retain the trace's reached checks and compose the actual continuation, including its own finish. A node or edge request must invoke only a strictly smaller body induction hypothesis, then derive its actual cell retention before the physical finish. Existing checked Running lemmas provide cell preservation and active-bound restoration from that same constructed trace.

The public general endpoint must discharge both smaller-body families internally. It must not accept BodiesBelow, a completed callback, a caller-supplied own-body done equation, or a future InputsThrough as its completion premise. The current file deliberately exports only preservation, derived request transitions, checked prefix completion, and the derived finite pure base case.

Initial legitimate premises for that endpoint remain physical cache validity, heap readiness, operation validity and loaded sidecar fields, original scope and source growth/history, actual reached WordRanges, structural Safe/Operands/Below, and the initial active-bound invariant. Empty memo tables derive the physical and active cache premises. Ready heap and initial loaded fields still require their actual source construction/allocator bridges. Unrelated source cache, GHC demand scheduling, and runtime-container correspondence are separate.

## Validation

Focused command:

`/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativePhysicalCompletion`

Result: terminal exit 0, 1086 jobs, no new warnings. Only the existing unused-input dependency warning was replayed.

Probe command:

`/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-recursive/allocated-native-physical-completion-probe.lean`

Result: terminal exit 0. Seven public theorem axiom checks use only propext, Classical.choice, and Quot.sound. Four kernel examples prove fresh self and empty source completion, direct requestKey-none field preservation, and physical finish without NodeProduced.

No older Lean source, Audit, documentation, Haskell, or Git state was changed by this work.
