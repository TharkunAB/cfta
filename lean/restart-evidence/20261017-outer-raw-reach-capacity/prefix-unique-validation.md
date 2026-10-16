# Raw completed-prefix uniqueness

The new frozen production source has 65 lines and SHA-256 `68d1a636ea25551dd088416d4fa305a9a3cfb4a98fda0a43409824375c1a6314`.

`stable_unique` compares two stable literal evaluations at the componentwise maximum of their ten independent sufficient bounds.
Both equations then describe the same literal worker call.
Injectivity of Outcome.done gives equality of the output and the complete caller state.

The public `node_call`, `edge_call`, and `descendants` theorems apply that fact to the existing graph-to-stable completion theorems.
Both supplied raw graphs have the same request, initial state, and fixed conjunction budget.
They need no semantic Context, finite-ordinary domain, Plan, headroom, or future body law.
Equality covers the complete checked native state, equality operations, merge memo, fourth memo, and both outer result tables.
It is not only heap equality.

This module extracts the previously checked `reach-audit-kernels.lean` fact into a reusable production API.
It imports only the existing PartialWorkerCompletion module.
It does not require physical soundness of arbitrary successful literal executions.
It does not prove that a raw prefix exists or that a whole Reach path has capacity.
The intended capacity adapter constructs one admissible prefix independently, then aligns any supplied completed raw prefix with that return.

## Validation

- Pinned strict Lean 4.34.1, all linters: direct source process finished with exit 0 and no diagnostics.
- Root-owned canonical `prefix-unique-canonical-1.log`: terminal exit 0, 1455 jobs. The only warning is the historical unused `inputs` dependency warning.
- Isolated imported public checks: exit 0, four axiom/full-signature pairs.
- Final canonical-import public checks: exit 0, four axiom/full-signature pairs.
- Isolated and final canonical-import integration checks: exit 0, one axiom/full-signature pair each.

Both standalone sources enable all linters, explicit proofs, universes, deep terms, full names, and one million print steps.
Final imported logs have no warnings, errors, sorryAx, omitted terms, or truncation.
The generic stable proof uses propext. The raw graph consequences use only the existing standard propext, Classical.choice, and Quot.sound dependencies.
There are no new axioms, sorry, or admit declarations.

`two_ordered_rows_align` compares two independently supplied edge/descendant prefixes for each of two source rows.
It first aligns the first parent's returned edge and complete state.
It then aligns the first descendant return, which is the second row's literal initial state.
The second parent and descendants consequently align at every intermediate and final complete state.
It takes no child result law, semantic receipt, range premise, or enclosing completed Rows graph.

Reproduce the final checks from the repository root:

```
env LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -D linter.all=true lean/restart-evidence/20261017-outer-raw-reach-capacity/prefix-unique-public.lean
env LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -D linter.all=true lean/restart-evidence/20261017-outer-raw-reach-capacity/prefix-unique-integration.lean
```

No older production file was edited. No Lake, Git, Haskell, or host execution was run by this component.
