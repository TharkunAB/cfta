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
with a new symbol and its child states. A symbol can occur at several arities.

## Sharing and cost

Apply edits to the persistent `Map` that already stores the rows. Untouched
rows and the unchanged parts of the map remain shared. Updating k rows takes
O(k log (n + k)) time for n original states. An empty edit map returns the
original automaton. Validation otherwise scans the complete
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

## Validation

A standalone check compared 76 edit batches with fresh `mkFTA` graphs. The
cases include additions, replacements, deletions, empty rows, equalities,
guards, refined symbols, and invalid graphs. Guarded terms agree with the
rebuilt graphs. Cyclic size counts and rank/unrank agree. The original graph
stays unchanged. An untouched row retains the same `StableName`.

With GHC 9.14.1 at `-O2`, build a chain of 10,000 states, then replace its
leaf row 100 times. Each replacement uses a different nullary symbol.
Compare `replaceRows` with `mkFTA` on the edited rows of the same graph.
Both paths validate each result. Totals include the initial graph build.
Cachegrind measures instructions; `+RTS -s` measures allocation.

| Operation | Instructions | Allocated bytes | Result checksum |
| --- | ---: | ---: | ---: |
| Rebuild the row map | 2,845,154,736 | 636,808,464 | 100 |
| Replace the row | 2,143,596,643 | 488,767,072 | 100 |

Row replacement uses 24.7% fewer instructions and 23.2% less allocation in
this case. Validation still scans the complete graph. This measurement does
not include generator index construction or solver work.

The eight standard benchmark cells retain their checksums against main at
`c0cc8a05`. The largest instruction increase is 0.43% in `enumeration-speed 1`.
Allocation differences are below 0.01%. A fresh `-O0 -Werror` build, all six
suites, Fourmolu, HLint, and cabal-gild pass. Jobs run serially through
heavy-management with a 12 GiB process cap and a 4 GiB test RTS limit.
