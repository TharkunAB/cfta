# Native physical probe preservation

Reviewed on 2026-10-18. This component adds `SourceCurrentNativeProbeHeap`.
The production SHA-256 is `f199768aae7599da807cb1653647a2714aaa50a1e35db5cbc8e135bbd836f169`.

## Contract and proof

The three public theorems are `code`, `node`, and `edge`.
They retain `InternedFreshOrdinaryProbeHeap.Heap` through the literal native executor's successful return.
The initial weak `SourceCurrentNativeOperationHeap.Good` carries physical native cells, constructor readiness, equality operations and fields, semantic readiness, and cost validity.
It does not require a native key semantic law.
The initial probe heap is a separate input.

The private mutual induction follows the actual consumed native steps.
It covers compiled Work, reads, requests, checked row bodies, finish frames, and optional binder construction.
A Work step derives `NoNewMu` from its current physical operands.
An optional binder uses the repaired callback construction's physical probe preservation theorem.
Neither case takes a future callee preservation law.
Warm cells use their retained physical operand and returned-value residency.

The generic `code` theorem takes static `Safe`, `Operands`, and `CodeFields` certificates for its input code.
The literal `node` and `edge` theorems derive those certificates from initial `NodeReady` or `EdgeReady`.
They require no `InputsThrough`, `Ranges`, future graph, future result invariant, finite Cap, or closed input.
The successful `.done` equation remains an explicit input.
These theorems preserve an invariant; they do not prove termination, compute sufficient fuel, establish language equality, or construct full outer execution.

## Existing support and discarded duplicate

The existing `SourceCurrentAllocatedProbeExposure.read_heap`, `head_heap`, and `forest_heap` already support available open inputs.
The existing `SourceCurrentAllocatedProbeRequired.requireAll` retains probes through actual selected Required execution without whole-forest closure.
The existing `SourceCurrentAllocatedProbeMerge.allocated_call_heap` covers the actual allocated Merge graph.
Root uses these existing results for lower and Parent composition.

A new open-probe draft duplicated these facts and was removed before publication.
Its two immutable executed snapshots and raw logs remain under `filtered-probes-open-direct-*`.
Attempt 1 checked the exposure fragment.
Attempt 2 failed in the later duplicate Required fragment.
Neither draft is a selected production or public result.

## Constructed integration

The fixture constructs a closed source with two distinct productive Mu operands.
Their rows share `leaf` and `pair`; the second operand also has an `extra` row.
It constructs the source heap, its semantic and probe invariants, and a valid populated equality descent operation record.
The native tables start empty.

`cold_recursive` checks the actual fuel-256 request at width 16, proves that the operands differ, and obtains a Mu result with a populated native node table.
It invokes the new literal node theorem at that exact returned state.
`warm_recursive` runs the same request at fuel 4 from the literal first returned caller.
It retains weak Good and the physical probe heap, and checks returned-value equality and unchanged native node count.
It makes no full-caller identity claim.
Both public statements are exact aliases of checked private witnesses.

## Validation and retained attempts

The selected native strict log is `filtered-probes-native-direct-1.log`; it is empty.
Its canonical log is `filtered-probes-native-canonical-1.log`, with 1809 successful jobs.
That build replays one unchanged unused-variable warning in `InternedFreshOrdinaryClosedCompletion.lean:24:5`.
The owned native source has no warning.
The public group `filtered-probes-public-1` checks all three public heads with explicit signatures, full proofs, and axiom reports.

The selected fixture strict group is `filtered-probes-kernels-4`.
The selected fixture printer group is `filtered-probes-kernels-public-2` with two pairs.
All selected printer sources set `linter.all` and the seven required print options, and use `#check @`.
Only `propext`, `Classical.choice`, and `Quot.sound` occur in the selected axiom reports.

Fixture attempt 1 failed on missing noncomputable declarations, projection reductions, and a value inequality proof.
Attempts 2 and 3 exit successfully but contain two unused-simp warnings.
The first fixture printer attempt repeats those warnings.
They are retained but are not selected clean checks.
A previous message incorrectly called attempts 2 and 3 empty before checking the byte count; this review corrects that statement.
Attempt 4 removes only the redundant simp arguments.

The runner executes each immutable snapshot with pinned Lean 4.34.1 and `-Dlinter.all=true`.
The inner worker records effective cgroup limits and checks 4294967296-byte memory.max, the same memory.high, and zero swap.
Every attempt uses its own log and limit receipt.

## Remaining boundary

Root owns the lower/Parent composition and the full outer prefix transport.
This component supplies their missing range-free native probe-preservation step.
It does not close general outer completion or the retained-used Mu callback reconstruction relation.
