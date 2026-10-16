# Read-only review of actual admission trace simulation

Date: 2026-10-16 07:39 CEST.

Reviewed SourceCurrentAllocatedNativeAdmissionTrace.lean, 234 lines.
Source SHA256:
`a2567bdfcceae6888bd0f7345f5a7088d0e74dec0712207a574dafeb83bb079e`.
Root reported direct Lean GREEN0. This review ran no build or source edit.
No material proof or scope defect was found.

## Dynamic certificate and physical effects

ControlCertified at lines 43-49 follows the actual current code. Its edgeBody
case retains the exact request scope, request coverage, and physical row-return
continuation. current at line 52 extracts admission at a node or edge lookup
before that instruction publishes a new cell. It does not read a future
result or infer a semantic law.

yielded_effects derives Good, SemanticReady, Extension, and next Fields from
the actual yielded step and its reached physical checks. These intermediate
facts are not supplied as desired postconditions. Primitive and optional
binder continuations use those derived facts at the actual returned machine.
A pending optional binder cannot match a given yielded step. Finish changes
memo cells while retaining the machine used by the admission certificate.

## Actual hits and started requests

The node and edge ready branches use physical cache readback. Actual lookup,
demand, ready inputs, and checked keys identify the exact stored request and
available/resident returned output. The source continuation therefore gets
physical residency for the same value and complete actual state.

Started requests use PhysicalCache.node_started or edge_started to identify
the request that was actually stored and demanded. Branches applies to that
exact request. Node body compilation occurs at the reached machine with
actual Good, SemanticReady, ready operands, and source growth/history.
Extensions compose from the original caller through that reached machine.
No same-parent language law or completed body is a premise.

Absent and busy observations at lines 162 and 195 are excluded only because
their literal step outcomes are not yielded. This is correct for a given
Trace.cons. It does not prove that such observations are impossible for all
states or that every request terminates successfully.

## Checked edge prefix

The edgeBody case uses FieldClosure.body_complete for the actual checked
prefix with its current operation validity and loaded fields. It obtains
the emitted code and returned operations, then uses body_bind for the actual
continuation. The machine is unchanged by this allocation prefix. The next
certificate therefore uses the same heap and the actual returned operation
state. The argument does not substitute an old eager edge interpreter.
Mismatched and rejected bodies retain their emitted sentinel code. They
supply no fabricated recursive child demand.

## Literal trace induction

Trace.covered at line 213 inducts the actual physical trace, including finite
prefixes that have not returned. Each cons derives the current publication
check from its dynamic certificate, applies step_covered, and then advances
the certificate using the literal yielded step. The induction threads Good,
SemanticReady, Fields, record growth, and issued history. It does not assume
final coverage, future successful children, or a desired final query law.

Branches at line 31 remains an explicit static source-certificate component.
Its nodes and edges fields contain local compile/body admission proofs, not
completed executions. This boundary is honest. The general theorem must not
be called a fully instantiated source query until those exact branch fields
are derived from concrete node and checked-edge certificates. The planned
CoveredQuery endpoint must retain actual physical traces and align the same
returned value/state; it must not replace static Branches by final coverage.

The module proves causal request admission. Contextual semantic laws,
physical result correctness, runtime forcing, and pending-publication
correspondence retain their separate proofs and contracts.

## Reviewed hashes

```
a2567bdfcceae6888bd0f7345f5a7088d0e74dec0712207a574dafeb83bb079e  lean/MicroCFTA/SourceCurrentAllocatedNativeAdmissionTrace.lean
97c0df6c92663c5aee01a8ca3b384640cdef31ce3146c7ae182d5fc0cc7c0e19  lean/MicroCFTA/SourceCurrentAllocatedNativeAdmissionCode.lean
ffb8b0ccae2b40438d3fc154f2d0b8f4f489cca2374b26dd5c623d9e87c89e75  lean/MicroCFTA/SourceCurrentAllocatedNativeAdmissionExecution.lean
c591e60800e2263dbd1d2e406bc3160b65c60a45d02249c840cb60c6d09988e7  lean/MicroCFTA/SourceCurrentAllocatedNativeFieldClosure.lean
776ec03bb93e0496a65983656ea674843d53ab1650cc6f45bbe3e7b05a6beaba  lean/MicroCFTA/SourceCurrentAllocatedNativePhysicalCache.lean
```
