# Repaired comparison correspondence and unfinished selection bridge

`MergedFreshOrdinaryComparison.check_eq` proves exact equality with the
previous ordered comparator for every fuel and ancestor list. Its premises
are actual source Facts, Prepared records, available operands, and closed
operand free-name sets. The repaired comparator uses repaired stored
reconstruction for every demanded read. Equality includes successful
Booleans, explicit failures, and the complete returned cache.

The proof retains ordered child conjunction, cover search, narrow reads,
and short circuits. `readRows_eq` isolates the complete read-and-cover step
before induction on comparison fuel. This decomposition avoids a kernel
heartbeat timeout in the direct recursive proof. The final checked module
needs no raised heartbeat limit.

The proposed corresponding child-selection bridge is preserved in
`MicroCFTA/MergedFreshOrdinarySelection.lean.incomplete`. It is excluded from
the aggregate audit. `any_eq` reaches a deterministic kernel timeout after
about 80 seconds. `retain_eq` then reports the missing `any_eq` constant.
Splitting out `compare_bind_eq` and `compare_context` did not resolve it.
The latest diagnostic is `/tmp/mcfta-fresh-selection.log`.
This is a proof-checking limit, not a source counterexample or verified law.

Restart by simplifying the `any_eq` proof term. Preserve the exact actual
comparison equation and make intermediate-state facts opaque to the larger
induction. Once the complete selection adapter checks, compose it through
cold columns, ordered groups, and the recursive merge worker. Existing
prepared cold proofs are unchanged. Their repaired reader and complete
comparator have exact bridges; the full repaired merge composition remains
the next explicit correspondence step.
