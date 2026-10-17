# Update a language from new facts

A language update produces a new explicit automaton. The old automaton remains
valid. The operation changes rows in `Data.CFTA.FTA`; it applies to ordinary,
equality-constrained, and liquid automata because their transitions differ
only in their symbols and annotations.

## Row edits

`replaceRows` takes a map from states to row edits and an existing automaton.
`Just transitions` replaces a row or adds a state. `Nothing` removes a state.
`Just []` retains a state that accepts no terms. A missing deletion is a no-op.
The initial state stays the same. Replace its row to change the root language.

Apply the whole batch before validation. This permits an edit to add a state
and a reference to that state together. Validate the initial state, every
child reference, and the arity of each symbol with the same checks as `mkFTA`.
An invalid edit returns an error and leaves the old automaton available.

To add or remove a transition, read its current row with `transitionsFrom`,
change the list, and replace the row. To add a constraint, use
`conjoinConstraints` on the selected transition. To change a refinement,
replace its refined symbol or annotation. A new constructor is a transition
with a new symbol and its child states. The batch must retain a ranked alphabet.

## Sharing and cost

Apply edits to the persistent `Map` that already stores the rows. Untouched
rows and the unchanged parts of the map remain shared. Updating k rows needs
O(k log n) map operations for n states. Validation still scans the complete
result. This first operation does not maintain a second index of references
or symbol arities.

Interning can reuse equal finished nodes when the new graph is imported.
The importer still traverses the graph and has its own state memo. A changed
cycle can require new recursive nodes. Do not assume that every unchanged
row yields the same physical node or that its descendants cost nothing to read.

Count tables and generator indexes describe one language. Build new indexes
for the updated automaton. Reusing per-state count tables needs dependency
tracking and invalidation through cycles; that remains a separate spike.
Solver memo reuse depends on the exact formula inputs and the solver scope.
The row update itself neither starts a solver nor changes solver state.

## Ranks

An edit can add or remove terms and change their ranks. A saved rank must name
the language version that produced it. Use the updated generator for both
ranking and decoding after an edit. The same updated automaton keeps its ranks
across processes under the same ordering policy.

## Validation plan

Compare each edited graph with a fresh `mkFTA` graph for additions,
replacements, deletions, empty rows, cycles, equalities, and guards. Check
invalid roots, dangling children, and inconsistent symbol arities. Verify
that the original graph stays unchanged. Compare allocation and instructions
for a small edit to a large graph with a complete rebuild, then run the
standard PR gate. Record the measured cost before publishing the API.
