# Completed trace induction helper review

`SourceCurrentHereditaryNativeTraceInduction.lean` defines the concrete source plain predicate, the completed-trace predicate `Preserves`, and three smaller-trace composition lemmas. The final source is the strict direct-5 version.

`Preserves` takes initial current-state facts, a local physical compiler certificate, actual equality-field availability, a local hereditary compiler certificate, and both causal stores. Its execution premise is the exact finite `Steps` trace to a pure result. Its conclusion retains the actual returned stores and the local result postcondition. It does not assume the conclusion of that trace as a separate law.

The helper theorems explicitly take the strong induction hypothesis for strictly smaller traces. The root completed-trace theorem discharges that hypothesis by induction on the actual trace length. This file alone is not a general trace preservation or completion theorem.

The bind lemma splits a supplied completed trace into its actual body and continuation at the same intermediate full checked state. Existing initial resources and the physical prefix theorem construct the body receipt. The smaller local induction supplies its result and stores. The continuation receives those exact outputs. Equality-field growth comes from the body receipt.

The node and edge lemmas split the body from its captured finish step. The finish frame consumes one actual step, so both local induction calls are strictly smaller. The protected-body theorem retains the exact evaluating owner through the actual body. The body result derives the annotation. That annotation derives a constant local law for its original request. The finish then installs that derived law at the retained owner. No future body result law, future final context, arbitrary warm producer, or separate selected body execution is used.

All five public declaration pairs pass. The integration kernel constructs physical and hereditary certificates for the actual compiled node body from initial original scope, source membership, bindings, operand annotations, and current stores. It applies the root completed-trace theorem to the supplied actual body trace, then performs its literal captured finish. The result includes the exact returned owner cell, both causal stores, the derived result annotation, and the actual source unconstrained gate. The kernel does not take the body's annotation or result law as a premise.

The first failed source used the reserved Lean token `local` as a binder. The next attempts exposed an unresolved control argument in the physical finish-step call. Those drafts and logs remain available. The final source uses explicit finish controls. One empty archival-copy log is retained under an explicit partial-copy name; it is not a validation result. Final public and integration logs are complete and clean.

The production modules are unchanged after canonical validation. The reviewed root Control and Trace dependencies are preserved as immutable source snapshots. This component does not prove general recursive selected outer progress, convergence, or full Haskell correspondence. General native completion and exact language conclusions belong to the separate root and cold-entry endpoints.
