# Ready edge cells at captured node-body returns

The new module is `SourceCurrentNativeWriterReadyRetention`.
The earlier `SourceCurrentNativeNodeWriterHistory` component stays unchanged.
The final new source SHA256 is `296e1ab435b07e703bd25f9f34f1804f4bad68409ef728a1f0348980170a59cd`.

`trace_retained` derives native `Retained` from an actual checked `Trace` and initial `Shape`.
It uses `SourceEqualityNativeDemandMemo.step_preserves` at each literal checked step.
`Retained.edges` retains each returned edge cell at its exact handle, request, and complete result.
This property is stronger than physical heap growth.

`Written` retains the exact captured node owner and original `NodeRequest`.
It retains the actual `compileNode` body trace, the protected owner at body return, and the exact finish trace.
It retains both writer heap growth facts into the reader heap.
It also retains `Retained` from body return to the reader's full native state.
`Written.forget` returns the earlier node-writer receipt.

`writers` derives these receipts from the existing actual `EdgeWriterGrowth.History`.
The proof follows actual completed traces from empty native tables.
Physical advances use their recorded past heap growth and actual `advance_retained`.
Lookup, demand, protected finish, and both request families use their actual retention theorems.
No caller supplies an output-writer law.

`edge_writers` maps every edge cell already returned at the captured body return into the final reader.
The final reader's `History.writers` then supplies that cell's earlier edge writer.
The consumer does not require `History` at the internal active node owner.

## Constructed check

The kernel builds its own closed source with an ordinary child and a productive Mu child.
It constructs the cold checked edge trace and an intervening physical edge allocation.
It then constructs a new root-node request at handle 2.
Its actual self-body returns at `rootStarted`, where edge handle 0 is already returned.
The actual finish trace derives `Retained rootStarted.native rootAfter.native`.
The final history supplies the exact earlier writer for edge handle 0.
The same check invokes `writers` and `edge_writers` for the new returned root-node cell.
The check has no supplied graph, future state, or desired writer premise.
It proves that an actual allocation occurred before this root-node call.
The root's self-body is a zero-step body. This case does not unfold the productive Mu child.

## Checks and limits

Strict source attempts 1 and 2 failed on exact-state casts and a shadowed handle.
The final strict attempt 3 exits 0 and its raw log has 0 bytes.
Canonical attempt 1 exits 0 and builds 1170 jobs.
It replays the existing ClosedCompletion unused-variable warning.
The selected public and constructed logs have no diagnostics or printer failures.
Public attempt 1 checks five declarations. Kernel attempt 2 checks one theorem.
Each uses all eight explicit printer/linter options and prints full proofs and axioms.
The selected checks use only `propext`, `Classical.choice`, and `Quot.sound`.
Kernel attempt 1 is preserved with its raw failure log. Its root key lacked a concrete identity.
Every run records effective MemoryMax and MemoryHigh of 4 GiB and swap limit 0.
The largest observed peak in this component is 607 MiB.

## Boundary

These theorems concern actual past checked executions.
They do not prove termination or construct an arbitrary completed query.
They retain `compileNode` output provenance. They do not equate this output with a recursive Mu callback result.
The body-return-to-reader cell map does not provide an internal lifecycle `History`.
It does not embed all earlier writer events into one global event trace.
General retained-Mu row alignment and whole outer-node progress remain separate obligations.
