# Literal Scan and full caller review

Reviewed at 2026-10-16 13:33 CEST. The review changed no proof source.

Reviewed hashes:

```text
fc1a933520838db4467dc2c7c037638c8f2f3ee98ddfd50944e54520f3c31aa1  SourceCurrentAllocatedScanWorker.lean
bd93e6e11f7db826d224c8f9406c9aee61093aef8692882195d48c4d421f25c2  SourceCurrentAllocatedScanCaller.lean
24170d7e672feced01aa0a34b346592a4b9e274637175eb35f30f8cf140e184b  SourceCurrentAllocatedScanWorkerActual.lean
```

No material defect was found.

The worker preserves the graph branch order. Primary false selects its
head and executes the suffix. Primary true executes secondary. Secondary
true skips to the suffix. Secondary false executes the first-seeded query
at the exact gate return and then the current conjunction call. True stops
before the suffix. False continues from the actual returned checked state
and fourth memo. Selection prepends a successful selected class and retains
the same prefix as nested tags on failure. The literal decision uses the
current conjunction worker; it does not use the historical emptiness body.

Caller.verified applies soundness, strict supplied-read validity, and probe
retention to the same actual graph. Its returned Post contains the same
computed inventory used for final admission. The returned physical Effects
derive fields, equality-cache growth, old request/result Sound, merge Stored,
and fourth-memo Correct. The merge value and both outer result tables are
retained by the literal caller advance. Native state can change through
checked queries; it is not incorrectly declared unchanged.

Caller.actual constructs strict reads for its actual graph. Caller.finite
constructs a graph from initial readiness and reached ranges before it
constructs those reads. The public premises contain initial Context,
available original values, proper paths, Nontrivial classes, and the reached
range plan. They contain no future semantic receipt or completed suffix.

WorkerActual.sound constructs a finite relational graph from physical
initial facts, then aligns it with the supplied literal success. The
unconditional uniqueness theorem identifies the entire result pair, all
checked fields, and the complete fourth memo. Its `Prod.mk.inj` step also
aligns the stopped class and exact selected list. WorkerActual.verified then
receives reads and Post for that same graph and state. WorkerActual.finite
uses the same constructed graph to supply stable literal bounds.

StoppedSound is scoped to class refutation under accepted original forest
semantics. It does not claim that a false conjunction answer proves an
accepted term. Selected lists retain order and repeated occurrences.
Logical global reads and host demand/publication remain explicit boundaries.
The external root probes and the two semantic integration kernels pass.
