# Common-cache language laws for cold merge

`MergedColdMergeLanguage` supplies constructor and column laws for the
cold operational worker. Every language in one law uses the same cache.
The laws do not transport the raw graph of an earlier cold cache through
allocation. They require no global `Ready` property.

`ordinaryUnion_common` proves that actual ordinary union has exactly the
union language of its operands when each operand is ordinary or empty.
It reuses `makeNode_exact` and exact physical edge records.
`ordinaryUnion_covers` composes this equation with a recursive result
that covers the new ordinary node.

`selected_covers` connects the actual ordered stateful selector to a
covering retained-column result. It interprets the selected and original
records in the same later cache. It uses the proved comparator semantics;
it does not assume that the comparison answers are correct.

`small_edge_covers` preserves the original label and guard after ordered
child coverage. `large_edge_covers` includes each original row after
positionwise column coverage and actual unconstrained edge construction.
`node_covers` combines the covered rows through the actual parent node
constructor. The large branch requires the selected top guard to accept
every term. `MergedPhysicalUnion.makeUnion_common` already gives the
exact retained-boundary union equation.

These are composition laws, not a termination theorem for the full cold
worker. Recursive coverage must be derived by the worker's ordinary-height
induction. The common-cache statements make that induction independent
of unproved raw cold-cache language transport.

The pinned Lean 4.34.1 build and imported-theorem axiom audit check this
module. The audit permits only `propext`, `Classical.choice`, and
`Quot.sound`. Its log is `/tmp/mcfta-cold-merge-language-audit.log`.
