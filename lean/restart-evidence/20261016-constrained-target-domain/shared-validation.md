# Finite ordinary shared-target validation

Validated at 2026-10-16 16:53 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryShared.lean`.
Source SHA-256: `bdd435bb202e4813586eee4104968a0ab7b7f55f5e03455f25a8584cd0166c91`. The module has 185 lines.

## Result

The canonical final focused build passed with 1299 jobs and terminal exit 0.
`shared-build-2.log` contains only the historical unused `inputs` dependency warning.
`shared-direct-1.log` passed with no diagnostics.

All nine public declarations have an axiom report and a full signature check in `shared-public-1.log`.
They comprise `Stored`, four lifecycle helpers, and four producer theorems.
All checks passed without errors, warnings, or `sorryAx`.
Two serial integration theorems have axiom reports and signature checks in `shared-kernels-2.log`.
That final check passed without errors, warnings, or `sorryAx`.
The failed first integration attempt remains preserved.

## Public endpoints

- `initial_stored` clears only the slots and retains the supplied native and merge certificates.
- `advance_stored` retains slots and merge certificates during native execution.
- `advance_heap_stored` preserves all three structural tables through constructor-only advancement.
- `store_stored` adds the proved output domain at its exact slot and retains earlier slots.
- `force` verifies the same actual Force graph and returns its existing full receipt, final Stored, and returned value domain.
- `force_finite` constructs that actual force from initial class and table facts plus reached ranges.
- `leaf` verifies the same actual Leaf graph and returns its existing full receipt, final Stored, and NodeNarrow from the current input to the returned value.
- `leaf_finite` constructs that actual leaf and derives the same structural conclusions.

## Integration checks

`force_then_hit` constructs a finite first force from initial readiness.
It uses the derived slot presence for the next literal hit.
The second call returns the exact same full shared state and value.
Its force range obligation follows from the existing slot; it needs no target range checks.
The actual hit read graph proves that its complete global memo bundle remains unchanged.
The stored structural certificate and returned domain survive both calls.

`two_leaves` constructs two finite leaf calls in sequence.
The second call uses only the first receipt's returned Ready, availability, globals, and Stored, plus its derived input domain.
Its additional range plan refers only to reached raw first-Leaf graphs.
It does not assume a future Ready, result law, successful second graph, or completion callback.
The two actual input-height bounds compose to the original input bound.
The existing language narrowing receipts also compose.

## Contract review

The private force proof handles a literal slot hit with `Stored.slots`.
A miss calls the frozen actual Target structural theorem at the same input and returned checked state and merge memo.
Current captured availability follows from `known` at the base heap and the Ready heap retention.
Current domain and coherent availability derive selected ForestClosed obligations and closed leaf input metadata.
No separate future path-closure or closed-result premise is supplied.

The Leaf proof applies `Execution.node_trace` to its own literal Step.run trace.
The request domain is the actual emptyDomain.
The returned height bound is the bound for the SECOND operand, which is the current leaf input.
Shared native certificates come from that same trace.
Slots and merge certificates survive the exact shared-state advance.

The full existing Force and Leaf receipts retain their readiness, computed admission inventory, availability, closedness, physical effects, heap and machine retention, warm merge state, actual global receipts, and language laws.
The new structural facts refer to those same output values and full states.
No equality to an older worker, historical execution transfer, future producer law, or future result invariant is used.

Guards and equality classes remain unrestricted.
The captured forest and the current Leaf input must belong to the finite ordinary domain.
Mu, reference, and explicit-union input records are outside that domain.
These endpoints do not prove the whole class-edit pass, general constrained recursion termination, pending merge publication, host lazy evaluation order, or Haskell runtime correspondence.

## Commands and scope

Direct checks use `/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean` with `LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean`.
Public and integration probes import the canonical final olean.
The parent ran the canonical build.
This task changed only the assigned new Shared source and its new evidence files.
It did not run Lake, Git, or Haskell checks, or change older proof modules, Audit, root documents, or older evidence.
