# Cached enumeration indexes

Upstream PR #103 changes `findExpandableUVars` in
`microcfta/src/Data/CFTA/Enumeration.hs`. The state now stores expandable
slot indices and raw waiting-reference counts. The scheduler resolves each
present waiting-map key through union-find before it removes blocked
representatives from the candidate set. Duplicate suspended references
increase a count. They do not require duplicate representative lookups.

The source audit found three value-slot mutation sites: initialization,
allocation, and `setUVarValue`. Other source mutations call the setter.
Assimilation writes the merged target first and eliminates the source
second. The proof follows that order.

`EnumerationWaitingIndex` models the sparse count map with integer values.
`bump` removes a zero-valued entry. `replace` decrements every old suspended
reference before it increments every new reference. `replace_correct`
proves agreement with the complete slot scan. Duplicate occurrences count
separately. `remove_nonnegative` proves that removing an old slot cannot
make a count negative. `stored_positive` proves that every retained map
entry has a positive count. `support_exact` identifies its exact raw keys.

`EnumerationExpandableIndex` adds both indexes to the existing enumeration
state. `initial_correct`, `allocate_correct`, and `write_correct` derive the
indexes for the actual mutation operations. A write uses the supplied raw
slot index. It does not resolve that index through union-find.
`Reachable.correct` derives both invariants from initialization and a trace
of allocations, valid slot writes, and effects that preserve the slots.
The final scheduling theorem therefore has no assumed cached-index
invariant. The successful live assimilation branch has the exact original
state projection and derives both indexes after its two writes.

`EnumerationIndexSource.assimilation_lift` also covers every successful
branch of the existing source assimilation action. Equal representatives
and already eliminated sources preserve the state. The live branch retains
the actual intersection and empty-result guard. `assimilation_waiting`
proves that the complete sparse raw waiting map is unchanged by moving the
source constraints into the target. This includes duplicate constraints.
Representative changes still affect which candidate is blocked.

`EnumerationIndexSelection.findIndexed_exact` follows the new waiting-key
fold through actual path-compressing representative calls.
`selection_exact` proves equality of the old and new `Option (List Nat)`
results. Candidate order is the increasing slot order. `none` still means
there are no candidates. `some []` still means every candidate is blocked.
The proof preserves both cases. It also preserves every canonical
representative. It does not require equal intermediate compression writes.

`selection_complete` obtains one sufficient finite bound for both scans
from a total source forest. It proves that both complete with the same
selection. `reachable_selection` instantiates the finite key view directly
from the derived count-map support. No finite example is used as a premise.

## Representation and source boundaries

The candidate and count maps use extensional finite-container interfaces.
`candidates` is the increasing finite view of the cached set in the allocated
slot domain. `WaitingKeys` states the standard map-key enumeration contract:
a listed key is exactly a present map entry. The equality theorem permits
any key order and multiplicity with that support. `referenceKeys` gives an
executable finite reference representation and proves its support from
mutation history. It is a specification view, not the optimized Haskell
map implementation or an algorithmic cost model.

The old `EnumerationState` driver remains the existing source model.
The new modules verify the added index operations and their scheduler
equivalence. They also lift successful assimilation actions to indexed
endpoints. They do not replace the whole driver with a second copied
implementation. Graph views and the recursive-boundary predicate retain
the existing graph-adapter contract. The Haskell container implementation
retains its external representation contract.

`EnumerationWaitingMachine.replaceWord_exact` now executes signed bitvector
additions in the count fold. Bounds on the full reference counts before
and after the slot write derive all intermediate decrement and increment
bounds. Under those endpoint bounds, machine updates give the exact integer
map. `replaceWord_correct` retains its sparse-count invariant. The source
does not check the endpoint bounds. Their validity for a runtime allocation
history remains explicit.

The four index modules build with Lean 4.34.1 in 23 jobs. The machine-counter
module also builds with the same pinned toolchain. The isolated dependency
audit permits only `propext`, `Classical.choice`, and `Quot.sound`. No Haskell
source changed. The inspected PR #103 write paths did not expose a defect.
