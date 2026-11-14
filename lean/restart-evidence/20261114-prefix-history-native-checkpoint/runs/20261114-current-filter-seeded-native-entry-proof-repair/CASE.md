# Filter seeded native entry: proof repair

Recorded: 2026-11-14 21:18 CET.

This new packet preserves the failed `20261114-current-filter-seeded-native-entry-draft`
packet. The original case note still defines the scope and remaining obligations.
No compiler was run here. Root must check this replacement before it receives
module credit. No live module, Git, board, Haskell, or original target was changed.
No Haskell fix was found.

Source SHA256:
`92f88db8606af249faac9d9a30ede6c3fd7b4ea483504c0c98c472faf12261f5`.

## Feedback addressed

The strict log is
`20261114-prefix-zero-and-filter-repair-check/SourceSynthesisCurrentFilterSeededNativeEntry.txt`.
It reports a Top normalization mismatch, an equation rewritten by case analysis,
three impossible lifted outcome equations, and two constructor pattern errors.

The actual checked step uses `SourceEqualityConstraintConstructors.top`.
`SourceSynthesisGeneralizeSyntax.top` is defined to be that exact value.
The replacement explicitly unfolds this definition in the transport of the
actual step equation. It does not assume a backend equivalence or change the
operation in a public statement.

Case analysis has already rewritten the yielded native step in the goal.
That branch now uses reflexivity. The other native observations produce a
lifted outcome that cannot equal a yielded outcome. Each branch eliminates
that impossible equality after expanding the lift.

The two `Operand.force` cases now use explicit `@force` patterns. They name
the already indexed result as well as the heap and graph. The ordinary case
pattern exposes only the last two fields.

## Interface and scope

Raw theorem headers match the original bytes for both public candidates and
the private native-publication helper. The comparison reads each header from
`theorem NAME` through the text before ` := by`.

- `current_initial_narrowing_history`:
  `882431d6345677780f091579e7589d9bf2ab970b3874878944f84e30cba6dc67`
- `first_node_publication`:
  `372e0064e1f995f1a2aa6825c9075770a0eb64a1bcca35db42d2e084afa9108d`
- `current_filter_seeded_native_entry`:
  `f608604b217d688baa6dc66862a8fd6d9bcbbf8f66685c4e41cc5f26d53a95c5`

No premise was added. The incoming checked state and actual returned endpoint
remain literal. The completed seeded graph remains an actual-operation input.
The source root visitor is not yet proved to reach that graph. The actual
suspended descendant query can use different values and paths.

The native correspondence still covers only its first node instruction.
The remaining allocated edge execution is not a plain native execution.
Candidate-projection Type provenance, the visitor-to-query connection, and
the full original finite-compatible-completion objective remain open.
