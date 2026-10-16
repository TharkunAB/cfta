# Literal first-seeded worker validation

Frozen on 2026-10-16 at 13:23 CEST.

The worker uses three independent projection, stored-read, and native bounds.
Each operand is a literal forest projection. It performs no merge and carries
no merge memo. The fold projects each head, executes its tail, and runs the
checked native request at that exact tail state. Its base projects the seed.
The seeded wrapper rotates `seed :: rest` to the graph list `rest ++ [seed]`.
Empty input returns Empty at the identical complete checked state.

Projection faults retain the complete lower Result and reached constructor
heap at the same equality operations and native tables. Native faults retain
the complete NativeDemand Outcome and its returned checked state. Failed
prefixes execute no continuation.

Completion derives stable bounds from actual finite Operand/Fold/Seeded
graphs. Native bounds come from each actual physical Trace's literal yielded
steps and checked done stability. No recursive completion callback or future
state invariant is supplied. The proof does not derive a physical Trace from
arbitrary native success. That direction belongs to the separate Sound module
under legitimate initial physical conditions and reached ranges.

Success stability is unconditional. Larger bounds preserve every completed
prefix and its whole checked state. Componentwise maximum bounds establish
whole-state uniqueness even for incomparable successful bounds.

Root ran the coordinated canonical builds: Worker 1185 jobs, Completion 1186,
and Stability 1190. Each reached terminal exit 0. Only the old unused-input
warning appears in those dependency builds. Final direct public checks passed
23 axiom probes and 23 signatures. Their axioms are limited to propext,
Classical.choice, and Quot.sound. Eleven named kernel compositions passed
with exit 0 and no warnings or sorryAx. The first kernel log had two unused
section-instance warnings; the second recorded a probe-only doc-comment
placement error. The final third log is clean. All attempts remain.

The kernels cover empty zero-fuel identity; singleton native bypass; complete
projection table and operation retention; exact unresolved projection state;
head and tail failure short circuits; native constraint errors; literal
head/tail/native order; three-path rotation; repeated path occurrences; and
whole checked-state uniqueness.

This is a completed serial source model. It does not establish GHC forcing,
host global-table execution, lazy publication, or outer recursive termination.
No frozen prior proof, Haskell source, Audit, documentation, or Git state was
changed by this implementation. Root manages source refresh and aggregate
validation.
