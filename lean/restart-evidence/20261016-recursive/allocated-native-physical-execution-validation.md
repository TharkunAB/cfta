# Physical checked execution validation

Frozen: 2026-10-16 05:14 CEST.
Source: `lean/MicroCFTA/SourceCurrentAllocatedNativePhysicalExecution.lean`.
SHA256: `b3e1bbd80c017212dddbbe18f27970c62a06c0a6ea44e1fed6e3680bdba114c5`.
The source has 327 lines. Older proof files were not edited.

## Proven endpoints

Namespace: `MicroCFTA.SourceCurrentAllocatedNativePhysicalExecution`.

- `Inputs` checks only current physical work operands, domain-entry operands, optional-binder availability, node/edge words, and actual running finish cells. A node range check is conditional on `requestKey = some key`. Direct unencodable requests require no packed-key bound. Node finish needs Available. Edge finish needs EdgeResident. No finish check needs NodeProduced, EdgeProduced, or a language law.
- `work_checked`, `node_step_valid`, `edge_step_valid`, and `step_valid` derive Kernel.Valid and both physical memo-family invariants through actual operations. Checked edge bodies retain the exact native state. All error, blocked, and yielded outcomes remain in scope.
- `step_extension` retains physical records, issued identities, and the domain cache through one actual checked step.
- `step_invariants` combines physical memo validity, machine Extension, and heap Keeps from initial physical Valid, initial RequiredCache.Ready, and the current Inputs.
- `InputsThrough` follows only actual yielded controls and full returned states. `execute_invariants fuel control state valid ready inputs` derives physical memo Valid, machine Extension, and heap Keeps on every actual finite execute outcome. It does not assume future validity or completion.
- `code_inputs code state operands words` derives the current Inputs from the frozen CodeProgress.Operands certificate and actual conditional Words. It needs no model, holds predicate, or Below premise.
- `inputs_heap` and `through_heap` expose the physical subchecks consumed by existing semantic-readiness and cost-preservation theorems.
- `node_busy_impossible` and `edge_busy_impossible` use physical captured-request identity, existing structural ActiveAbove, and a strict independent requiredFuel bound to exclude an actual busy demand. They use no old native validity or semantic Produced assumption. The node bound here is applied only to an actual memoized lookup, so its explicit KeySafe premise is supplied by that lookup's present key and reached word check.

The public theorems do not assert equality-operation validity or final sidecar fields. They retain the actual full state used by checked execute. Existing allocation/field proofs must supply those separate invariants.

## Commands and results

Focused build:

`/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativePhysicalExecution`

Result: terminal exit 0, 1080 jobs. No new warnings. The pre-existing unused-input warning at InternedFreshOrdinaryClosedCompletion:24 was replayed.

Public dependency and kernel probe:

`/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-recursive/allocated-native-physical-execution-probe.lean`

Result: terminal exit 0. All 12 public theorem checks use only propext, Classical.choice, and Quot.sound. Six kernel examples check direct requestKey-none publication, node and edge physical finish, body failure/blocking preservation, the model-free current-code bridge, and reached heap-check transfer.

## Exact remaining completion hook

This module proves physical preservation, not general checked completion. InputsThrough remains an explicit reached current-input plan. It supplies neither a completed recursive callback nor future cache validity. A general completion theorem must derive this plan together with the actual return by structural code induction and strong induction on independent requiredFuel.

At recursive requests that proof must use the physical cache's ready/start receipts, exclude absent handles from physical Shape, exclude busy handles with the new strict-bound lemmas, recurse only into the actual checked child program, retain its physical output availability, and preserve its own running finish cell. The existing checked Running lemmas restore enclosing ActiveAbove after the actual finish. Accepted and rejected edge branches must remain separate: rejection has no child calls. Initial loaded equality fields, actual word ranges, and initial ready/active conditions remain genuine independent premises. None is replaced by an old eager Evaluation, Produced fact, old scoped Step, or desired result language.

The independent schedule is the recursion measure. Its semantic source interpretation does not assert native result meaning. The contextual Mu/body language induction remains a separate obligation.
