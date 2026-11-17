# Explicit implicit-index binders in the mutual motives

Status: COMPLETE PROOF-ONLY REPAIR, UNCOMPILED. Root alone checks the module.

The authoritative checked source has two errors at lines 498 and 507.
Both are in the recursor motives. This source has no enrich_output declaration.
QualifiedOutputHistoryAt and QualifiedPreparedHistoryAt have implicit visible
indices. In the old lambda, `fun depth ...` skips those implicit arguments and
binds depth to the first explicit OutputHistoryAt proof. JointOutputLedgerAt
then receives a proof where it requires Nat.

This repair adds braces to each of the eight implicit visible-index binders in
both motives, in both recursor applications. The explicit original-history and
qualified-history proof binders stay unchanged. All constructor handlers, the
captured callback elimination, the worker wrapper and every other byte remain
unchanged. The proof still uses one qualified derivation for each joint ledger.

Both public headers db19cbe0/469e90c8, complete definitions c9409cbe, the private
captured helper header, all observations/endpoints/fuels/indices and probes are
byte-exact to the original frozen packet. The patch changes exactly four lines.
No runtime argument, logical premise or result changed. No compiler, Source,
Audit, Git, board, temporary path or proof-limit action was performed.

The original failed packet and check remain immutable and have zero proof
credit. This repair has no proof credit until a strict module exit 0 without
sorryAx. Literal operation history does not establish historical Holds, native
membership, TypeIn, guard truth or one finite compatible assignment.
