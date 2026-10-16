# Covered query review

Date: 2026-10-16 07:43 CEST.
Review mode: read only. No Lean source changed. No build or probe ran.

## Verdict

No material defect found. The single-query causal coverage gap is closed
under the stated initial invariants. `query_complete` derives final
all-phase `Covered` from actual checked execution. It does not require
coverage, a result law, or successful child execution at the final state.
`generated_complete` retains that result for the literal expanded input
inventory. Complete generated-history and seeded-fold composition remain
separate proof targets. They must no longer be described as a missing
single-query causal coverage theorem.

## Checked proof chain

- `CoveredQuery.branches` (line 30) supplies concrete node and edge
  certificate proofs. The public query theorem has no abstract branch
  preservation callback.
- `AdmissionCode.Certified` (lines 25-49) requires current source scope and
  input/seen admission at each node or edge instruction. Its recursive
  continuations use physical validity, growth, semantic heap validity, and
  returned availability or edge residency. They do not require a child
  language law or future query completion.
- `AdmissionNodeCertificates.node_certified` (line 194) covers every
  literal dispatch branch. Reset uses empty seen coverage. Swap retains
  seen coverage and reverses the operands. Union and row branches derive
  exact member/child admission from parent admission. Mu entry uses actual
  `Environment.enter` readback and `request_entered_seen`. Reference
  branches identify the literal current binder read with the retained
  original source record. Empty, self, repeated, and failed branches do
  not introduce an unproved recursive admission obligation.
- `PairAdmission.entered_seen` (line 99) uses the two actual physical
  identity equations. It covers the canonical min/max pair and preserves
  all old seen pairs. This does not assume pair names are admitted because
  a conditional result law holds.
- `AdmissionEdgeCertificates.body_certified` (line 87) uses the actual
  checked body yield and exact unchanged native machine. Stopped branches
  certify the sentinel. Accepted branches use the literal ordered child
  zip, with no whole-result admission or guard truth premise.
- `AdmissionTrace.yielded_certified` (line 78) follows actual instructions.
  Direct node requests compile their exact request. Ready and started
  memo branches use physical request exactness. Checked edge-body
  allocation uses the actual emitted code and returned operation state.
  Finish instructions retain the original request. The proof never
  substitutes an old eager execution for this checked trace.
- `AdmissionTrace.Trace.covered` (line 213) checks admission before each
  actual lookup publishes a cell. The invariant in `AdmissionCache`
  applies to every stored cell, including suspended and evaluating cells.
  Status, demand, and finish retain the same stored request.
- `CoveredQuery.query_complete` (lines 49-84) obtains completion from the
  established warm-query theorem. It then applies the concrete admission
  simulation to that same receipt's physical trace. This is not circular:
  warm completion does not assume final coverage, and admission propagation
  does not assume the root or child language conclusion.

## Actual generated inventory

`CoveredQuery.generated_complete` (lines 97-161) exposes the exact target
heap, `roots ++ [left, right]`, and its availability and closedness proofs
in the conclusion. Its `finiteInput` is the literal inventory computed
from these witnesses. Target originals and new root admission are derived
from the coherent target heap and closed resident roots. They are not
supplied as desired model-validity answers.

The theorem derives old-to-target input/rank agreement from actual heap
growth and issued history. It rebases both contextual returned laws and
all-phase request/seen coverage on the same checked state. The following
query uses that state with reflexive target growth. It does not reset any
native or operation table. Its returned receipt carries final coverage
for this same computed target inventory, so this coverage can feed a later
inventory expansion.

## Retained boundaries

Initial `Good`, contextual cache laws, all-phase `Covered`, scoped cache,
semantic heap validity, idle state, source growth, and issued history
remain explicit warm-state premises. Cold empty-table coverage is derived
separately by `AdmissionCache.initial_covered`. Actual reached machine
word ranges remain an explicit per-query premise. Fixed-model queries
also require source-original, source-resident, closed, admitted operands.
Generated queries derive original/admitted operands in the expanded
current-heap inventory from supplied current availability and closedness.

The result is an actual checked native query theorem. It does not prove a
complete dynamic generated-query history or seeded class fold. Those
targets still need their ordered projection/query composition, reached
ranges, and semantic subtree inclusion. It does not establish global
unsafe-IO, machine-key capacity, GHC thunk forcing, or whole constrained
caller completion.

## Validation evidence inspected

`covered-query-build-final.log` records successful canonical completion of
1139 jobs. Its only warning is the preexisting unused `inputs` binder in
`InternedFreshOrdinaryClosedCompletion`. This review did not repeat the
build.

Reviewed source SHA256:

```text
aaacfcfbe966ff0f90cefbf9d7e5f6580e27684af1725a79af801c19e16de30d  SourceCurrentAllocatedNativeCoveredQuery.lean
a2567bdfcceae6888bd0f7345f5a7088d0e74dec0712207a574dafeb83bb079e  SourceCurrentAllocatedNativeAdmissionTrace.lean
97c0df6c92663c5aee01a8ca3b384640cdef31ce3146c7ae182d5fc0cc7c0e19  SourceCurrentAllocatedNativeAdmissionCode.lean
7d56d8e6116cf35dff25bbf99b3d821c6ae883a67e07fddcf43ea041afd9755b  SourceCurrentAllocatedNativeAdmissionCache.lean
ffb8b0ccae2b40438d3fc154f2d0b8f4f489cca2374b26dd5c623d9e87c89e75  SourceCurrentAllocatedNativeAdmissionExecution.lean
79c76e0434a56de6a9b011f9c6e6a5f28edbb85ecc5c2d07311b6408ca138e9e  SourceCurrentAllocatedNativeAdmissionNodeCertificates.lean
e9b59bec554c83387b6627ca78c75528432dc83bf1e94eaad44ce4d428dcb4a2  SourceCurrentAllocatedNativeAdmissionEdgeCertificates.lean
2889fc2981569a36f9d5dc414045e72b6a276f9dc46aee12e4460cce2aba48f0  SourceCurrentAllocatedNativeRequestAdmission.lean
2a0221ba9257ddadac067e86e552f9ba2f498a20c88753986a389e0b9e9c8a12  SourceCurrentAllocatedNativePairAdmission.lean
```
