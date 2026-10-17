# Original-input exchange from actual raw absence

The production source is `SourceCurrentNativeInputExchange.lean`.
Its SHA256 is `8768039795ac792cd437805e3eb3c74b9682f48236e1b35f31f0f5308fc36e44`.

`live_agreement` derives its live-input relation from one actual raw result.
Each changed varying reference must be absent from that result's free names.
Fixed captures can be arbitrary available records, including open Mu records.
`of_completed` compares two completed full source executions in a common coherent extension.
`complete` constructs the changed execution from its initial later Context, DepthHeap, and complete payload coverage.
It uses the existing full source completion theorem and live-input replay.
It returns the same literal Value, actual final heap, heap growth, and final Context.
`local_complete` specializes this producer to one varying reference beside fixed captures.
No public producer assumes successful completion of the changed run.
No public result equates the two final heaps.

Strict attempt2 passed with an empty raw log.
Canonical target1 passed with 322 jobs.
The selected public log is `input-exchange-public-1.log`: four full signature, proof, and axiom groups.
The selected integration log is `input-exchange-kernels-3.log`: two signature and axiom groups.
Both probe sources contain all eight required printer and linter options.
The selected logs contain no errors, warnings, omitted proof marker, or `sorryAx`.
The axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.
All runs used a 4 GiB MemoryMax, 4 GiB MemoryHigh, and zero swap.

The first integration builds two nested Mu constructors from empty caches.
It changes a syntactically used input in discarded edges.
The producer constructs the new run and proves an increased edge counter with the same returned Value.
The second integration retains a smart nested Mu with a free fixed capture.
It constructs the changed run and preserves the same stored Mu record.
A literal warm request returns that record even when its unused callback would return pending.
The original full program then replays at the exact returned heap without allocation.
Both integration theorems have no caller premises.

The raw-free absence premise is essential to the current proof.
Normalized callback `noDeep` does not supply it: `.var 0` still has a live raw input.
Root union filtering can also erase a live raw input after execution.
This module does not prove the general unused-local smart body equals the erased ordinary probe.
It does not derive complete native row provenance or outer recursive progress.

Failed direct attempt1 and integration attempts1–2 remain as exact source snapshots and raw logs.
They are historical failures and are not selected validation results.
No earlier source, evidence package, Haskell source, Audit file, or root document was changed.
