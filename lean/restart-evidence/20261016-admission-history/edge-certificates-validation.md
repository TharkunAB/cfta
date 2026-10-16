# Checked edge-body admission certificates

Frozen source: `lean/MicroCFTA/SourceCurrentAllocatedNativeAdmissionEdgeCertificates.lean`.
The source has 124 lines. SHA256:
`e9b59bec554c83387b6627ca78c75528432dc83bf1e94eaad44ce4d428dcb4a2`.
No old proof source, Haskell source, Audit, documentation, or Git metadata
was changed by this task.

## Public API

All three theorems use namespace
`MicroCFTA.SourceCurrentAllocatedNativeAdmissionEdgeCertificates`.

```text
children_certified source facts holds inputs request scope known combined
  state valid semantic ready
sentinel_certified source holds inputs left state valid
body_certified source facts holds inputs request scope known
  before after code valid semantic ready yielded
```

`facts : Facts source` refers to the fixed source heap.
`inputs : FiniteInput (view source holds)` is the fixed input interface.
`scope : EdgeScope source request` and
`known : EdgeCovered inputs request` admit the original ordered child lists
and the incoming seen pairs. `valid`, `semantic`, and `ready` describe the
current machine. They do not describe a future result.

`body_certified` consumes the literal actual receipt:

```lean
SourceEqualityNativeDemand.body request .pure before =
  .yielded (.code code) after
```

It derives:

```lean
SourceCurrentAllocatedNativeAdmissionCode.Certified source holds inputs
  code after.native.machine
  (fun final value => EdgeResident final.heap value)
```

The full authoritative inferred signatures are printed in the public probe.
No `NodeProduced`, `EdgeProduced`, parent result language, desired returned
law, future completed callback, or final Good premise occurs.

## Proof route and exact branch scope

`children_certified` follows the actual zipped original child order.
`RequestAdmission.child` derives each request's original scope and input
membership before its result exists. The parent seen coverage is unchanged
in each child domain. The walk consumes only actual returned availability
from the AdmissionCode callback. The final edge request uses the literal
combined constraint readback. `work_done` and `edge_verified` derive the
resident edge in its actual returned heap.

The fixed source `Facts` premise is necessary for this route. EdgeScope
retains original row residency, and source cached-record facts derive each
original child's availability in that source heap. Current facts alone do
not derive availability backwards in the fixed source.

`sentinel_certified` supplies the actual empty child and has no recursive
request. `body_certified` first derives native-state equality from
`body_native`, then inspects the literal checked body. Arity mismatch,
rejected, and mismatch-result branches use the sentinel certificate.
Accepted branches use the literal combined-value child code. Error and
blocked branches cannot satisfy the supplied actual yield equation.

Equality-operation effects stay in `after`. The theorem does not replace
that state, claim those effects are absent, or require a final operation
invariant. Guard truth, matching symbols, and whole child-language laws
are unnecessary for this admission and residency component.

## Validation

Direct pinned command before the canonical slot was released:

```text
env LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/SourceCurrentAllocatedNativeAdmissionEdgeCertificates.lean
```

Result: **PASS, exit 0, no warnings**.
Log: `edge-certificates-direct-1.log`.

Canonical command after root coordination:

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeAdmissionEdgeCertificates
```

Result: **PASS, 1107 jobs, exit 0**. Only the old
`InternedFreshOrdinaryClosedCompletion.inputs` warning was replayed.
The new source has no warning. Log: `edge-certificates-build.log`.

Public/kernel command:

```text
env LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-admission-history/edge-certificates-publicprobes.lean
```

Result: **PASS, exit 0, no warnings**.
Log: `edge-certificates-publicprobes-2.log`. Three public axiom reports use
only `propext`, `Classical.choice`, and `Quot.sound`; three complete public
signatures are printed. Seven kernel examples pass. The first probe log
retains a repaired empty-build equation proof and is not validation evidence.

The concrete source row is built with actual `makeEdge` and Top fields.
Its ready operation state comes from actual `emptyField`. Kernel reduction
checks the checked body yield, then the public body theorem certifies that
exact emitted code and returned machine. Other examples cover the sentinel,
accepted empty child walk, native-state retention, and literal arity
mismatch before field loads. The mismatch fixture checks source branch
selection only; it is not presented as a resident malformed-row execution.

## Remaining scope

The actual body yield remains explicit. This theorem does not prove body
completion, current field representation, execution-wide request coverage,
or a result-language law. Root's physical completion and admission trace
proofs supply those separate interfaces. Runtime forcing/publication,
container correspondence, machine capacity, and general outer constrained
termination remain separate source bridges. No Haskell defect or repair
was found or made.
