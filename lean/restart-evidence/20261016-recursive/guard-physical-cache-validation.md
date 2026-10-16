# Physical native cache lifecycle

Checked on 2026-10-16 at 05:13 CEST. The source file is frozen.

## Source and scope

`lean/MicroCFTA/SourceCurrentAllocatedNativePhysicalCache.lean`

SHA256: `776ec03bb93e0496a65983656ea674843d53ab1650cc6f45bbe3e7b05a6beaba`.

`Valid state` contains Kernel.Valid and both actual FlatMemoThunk validity records.
Each node cell retains NodeReady for its original complete request. Returned node
cells retain Available for the returned value. Edge cells retain EdgeReady and
returned EdgeResident. The records include original checked keys and handle bounds.
These predicates are generic in Symbol and Guard. They do not require DecidableEq.

The initial, lookup, demand, advance, and finish laws preserve these conditions.
Finish uses the literal current evaluating handle and returned physical residency.
No lifecycle law assumes NodeProduced, EdgeProduced, or a result language.

`node_request_exact` and `edge_request_exact` recover complete original requests
from the physical key and resident records. `node_ready_receipt` and
`edge_ready_receipt` prove exact ready-hit state equality. `node_ready` and
`edge_ready` derive stored request equality and result residency from actual
lookup and demand equations. `node_started` and `edge_started` identify actual
started requests. Running hooks preserve other active cells. The completed
cell itself changes phase at finish.

`of_provenance` is a one-way adapter from the stronger existing provenance
invariant. Its concrete source types need their existing DecidableEq instances.
No physical lifecycle theorem uses this adapter as a premise.

## Validation

Focused command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativePhysicalCache
```

Terminal exit 0. 1058 jobs. The only warning is the existing unused `inputs`
binder in InternedFreshOrdinaryClosedCompletion. No new warning occurs.

Probe command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-recursive/guard-physical-cache-probe.lean
```

Terminal exit 0. All 27 public axiom probes use only permitted Lean foundations:
propext, Quot.sound, and Classical.choice where inherited. Seven signature
checks and 20 examples pass. The examples execute the actual typed node and
edge tables. They check cold publication, suspended-to-running demand,
completion, warm lookup, warm demand, separate counters, and physical validity.
They also check that another finish cannot overwrite an already returned cell.
No native_decide, admitted proof, or custom axiom occurs.

Artifacts in this directory:

- guard-physical-cache-source.lean.txt: exact frozen source copy.
- guard-physical-cache-build.log: focused canonical build output.
- guard-physical-cache-probe.lean: checked proof and execution probes.
- guard-physical-cache-probe.log: terminal probe output.

## Remaining obligations

Actual checked execution must derive current physical operand checks and the
returned residency used at finish. The separate PhysicalExecution module owns
that induction. This lifecycle component does not prove that recursive bodies
finish, that a returned value has the intersection language, or that source
allocation tables cover every original field.

Machine key bounds remain explicit at lookup and request equality. The model
still requires the source identity capacity and no-reuse correspondence. It
makes no claim about global unsafe IO, GHC publication, blackholes, races, or
runtime forcing. The separate equality-operation State is not changed or reset
by these native-table laws. This module does not assert validity of that State.

Only this new Lean module and owned evidence files were written. No prior
proof, Haskell file, Audit file, restart document, or Git metadata was edited.
No owned process remains.
