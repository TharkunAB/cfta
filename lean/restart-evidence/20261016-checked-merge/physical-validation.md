# Allocated merge physical effects

The source is frozen. The owned proof file is `lean/MicroCFTA/SourceCurrentAllocatedMergePhysical.lean`.

## Result

`SourceCurrentAllocatedMergeGraph.Call.verified actual ready stored available` derives `Effects before after`, `Stored after.heap saved`, `Available after.heap output`, and `input.free = [] → output.free = []`.

`SourceCurrentAllocatedMergePhysical.call_complete clear input before memo ready stored available` constructs an actual allocated `Call` and these same returned facts. It uses the proved finite heap-only call and the exact `call_lift`. It does not assume recursive completion or a completed output.

`Graph.Run.extends` and `Graph.Call.extends` retain every earlier completed merge entry.

The public call endpoint needs no initial Top load, input closedness, whole-forest closedness, final field invariant, or recursive callback premise. `Ready` checks the initial semantic heap, stored CostHeap, equality-operation validity, and existing resident field loads. `Stored` is the explicit initial warm memo invariant.

## Mechanism

`SafeCode` checks raw work against the current operation cache. Its `grows` lemma transports each check through actual equality-cache growth. `body_safe` derives small-row guards from original resident edges and the current physical field heap. The large branch has a distinct `topRow` instruction. Its actual `emptyField` operation derives Top availability through `ConjunctionFieldAllocation.empty_field`; all old fields then grow to that same cache. Actual constructor work preserves the resulting physical annotation heap.

The mutual `Run`/`Call` induction threads exact states. A miss derives its body certificate, executes its actual nested calls, records completion with keep-first, and reads the winner. A hit returns at the identical physical state. The `Run.verified` helper has explicit static instruction checks; the public `Call.verified` endpoint discharges the body checks internally.

## Validation

Canonical command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedMergePhysical
```

Terminal status: 0, 1099 jobs. `physical-build-1.log` preserves output. There is no new warning. The only replayed warning is the existing unused `inputs` warning in `InternedFreshOrdinaryClosedCompletion.lean`.

Public proof command:

```
LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-checked-merge/physical-public-probes.lean
```

Terminal status: 0. `physical-public-probes-2.log` contains seven public axiom checks, seven full signature checks, and nine kernel examples. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Examples cover actual Top allocation, old-field growth, the literal topRow state, exact unchanged hit state, hit readiness, merge-table retention, empty-input completion, and the unchanged open-ordinary body branch.

The initial probe failed only because a generic `empty_field` invocation omitted the explicit `Formula` argument. Its raw log is retained. Earlier isolated proof/header drafts and their logs are retained as development evidence; they are not imported by the proof library.

## Source and scope

`cfta/src/Data/CFTA/Interned/Operations.hs:611–644` defines the memoized merge, small recursive rows, grouping, and column behavior. The new graph retains the completed column-first serial schedule and allocates the canonical empty field at the large raw Top row. Erasure preserves its exact constructor heap, output, and completed merge table.

This module proves physical effects in the allocated graph. The root checked-state adapter retains native node/edge/domain tables and transports `Good`, `At`, scopes, and idle status from those exact effects. It is separate from this file.

The source HashMap iteration/allocation correspondence, lazy publication before body completion, pending ancestor thunks, concurrent winner selection, GHC demand order, machine identities/capacity, and global unsafe IO correctness remain explicit boundaries. This result does not prove a fixed global merge fuel bound, whole caller termination, or language correctness. Existing independent language and global-memo receipts can use the exact erased call. The comparison predicate remains explicit; the literal source predicate adapter is separate.
