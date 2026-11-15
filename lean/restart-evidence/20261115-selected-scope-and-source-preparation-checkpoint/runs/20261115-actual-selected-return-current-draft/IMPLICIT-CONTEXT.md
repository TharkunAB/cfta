# Implicit context

All new declarations use the existing source Symbol and symbolic Constraint. Width is bits + 2. Metadata and worker output typing are Unit.

The return-point definition has no equality-class premise. It is noncomputable because the existing mathematical `advance` forecast is noncomputable.

The runtime and Current proofs use the existing DecidableEq Symbol, DecidableEq EdgeKey and DecidableEq Node context. The work proof explicitly omits all three equality instances. It uses only the pure task and frame recurrences.

The Current transition is specialized to the selected ledger constructor's immutable arguments. A driver can decompose that constructor and pass its stored snapshot, parent ledger and own receipt. The theorem does not take a new universal correctness function for the ledger or any future source endpoint.

The Origin constructor stores only source data and an actual inner tuple-nil Origin. It stores no Packet, Fits, Heap, Inputs, Current or reservation proof. It records entry to the literal stored parent-tail program. Its declaration does not assert that the remaining parent tail succeeds.

The current inner tuple has the genuine local scope: stored row-entry caller, actual row-own cache and actual staged child pairs. The returned tuple has the stored outer scope: outer original caller, outer original cache and outer full input list. These scopes are not identified or replaced by a subset argument.
