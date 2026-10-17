# Allocated Merge numeric replay review

Reviewed on 2026-10-17 at 10:30 CEST. The production source is frozen at `bc1bd2165d633543604f0b8781b0f022d9e4c73028592a226037f28dc52dc20e`.

The erasure induction preserves work fuel and selection fuel instruction by instruction. It includes failure observations. A Top row performs the literal empty-field allocation in the allocated worker. Its erased instruction performs the same constructor work at the same work fuel. The bind proof recurses from the actual returned intermediate constructor heap and memo.

The replay proof first uses erasure to exclude an allocated failure at a successful erased fuel pair. It then compares the computed allocated success with the supplied actual allocated graph at a common larger fuel pair. Existing stability and deterministic execution identify the entire returned allocated state and memo. The proof does not infer equality-state equality from heap erasure alone. Graph-relative completion is derived inside this proof. It is not a caller-supplied future numeric bound.

`of_call` transfers the existing initial scalar uniform bound to this exact allocated return. `complete` constructs the actual allocated graph from initial Ready, physical memo storage, operand availability, and Fits. It retains physical Effects, Ready at the returned state, the actual completed memo, result availability, conditional closedness, heap Fits, output mass, and exact replay at all larger fuel pairs. It has no supplied completed execution or desired output law.

The public probe has seven axiom/signature pairs. The constructive probe has three pairs. Both final logs are free of diagnostics. The production strict log is empty. The single canonical target passed 1313 jobs. The canonical log can replay the previously recorded ClosedCompletion warning; the new source is strict-clean.

The constructive checks have these scopes:

- `top_allocates` executes an actual Top-row instruction at work fuel 1 and selection fuel 0. It proves one new equality field and one new edge. The equality descent table is already populated. The result retains that table and the combination table exactly.
- `recursive_large` builds its own closed source with a five-row group, a productive Mu child, and a real union child. It derives initial physical and equality-field readiness. It then constructs its own full allocated call at symbolic computed fuels. No actual Merge graph or successful future worker call is supplied.
- `cold_then_warm` starts from that produced call. It derives the stored first winner and runs a second numeric call from the first exact returned state. The complete equality state and memo remain unchanged on the warm hit. A populated equality descent cell remains present.

Fits and the output-mass bound concern the constructor heap. These results do not give a numeric bound on equality-operation tables. Exact equality-state retention is separate from such a bound. This module closes full allocated Merge replay. It does not construct the complete initial Target forecast. The source graph models completed serial stages. Host forcing, lazy publication, pending memos, and whole-library correspondence remain separate obligations.

Every failed source and raw diagnostic log is retained. The final source, public probe, and kernel probe match their recorded snapshots.
