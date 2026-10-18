# Actual Head rows from selected native results

The production source is `SourceCurrentRecursiveHeadRowOrigins.lean`.
Its SHA-256 is
`163ea355c8a595b9e53f194266c77dc30749acb48a71bed2c89fc1e6fb2f9c12`.

## Produced result

`complete` takes one initial `Ready` heap and one available closed value.
It constructs the actual `Head`, full returned heap, `Keeps`, availability,
closedness, ordinary shape, and `HeadRows`. It takes no future Head, exposed
body law, callback relation, source-row trace, Cap, or whole-forest closure.
Closedness is local to this requested value. Other heap records can be open.

For an ordinary value, every selected output row retains an original source
row index and the same complete row. For a union, every selected output row
has an original member index and an exact epsilon `Origin` from that member
at the returned reader heap. Empty and reference Heads have no selected
rows. Canonicalization can reorder or remove rows; the statement maps an
output index to a source occurrence and does not equate the two row orders.
Each retained complete row includes its full guard and ordered children.

For a Mu value, `MuRows` retains the first literal stored-body `execute`
with the exact original own-name replacement map and actual intermediate
heap. The proof derives growth from that intermediate heap to the final
Head reader. The same selected Mu unfolds to the same complete result at
that final reader with no further heap change. Every selected Head row has
an exact epsilon origin in this actual returned execute result. This also
covers the collector fallback, rather than only the first ordinary fast
path. No future unfold completion or desired replay equation is an input.

`BodyRows` derives node and union reconstruction from the actual body call.
It retains either the exact closed identity shortcut or the existing open
`NodeRows` / `UnionRows` receipt. These receipts retain original indices,
full guards, and ordered actual child/member calls at their literal heaps.
Empty and reference body calls have their exact values and unchanged heaps.
A nested Mu body remains explicit: `BodyRows` gives no further relation in
that case. The literal execute, final replay, and selected epsilon origin
remain present in `MuRows` even in this residual case.

`query` consumes an existing actual checked query receipt, initial `Good`,
initial native writer `History`, and closed operands. It derives the final
native history and actual captured returned node cell and writer, then
constructs its subsequent Head. The captured writer can precede a warm
query. Its returned value supplies the literal stored Mu body; the proof
does not replace that body with a newer candidate callback. The query
receipt itself comes from existing query producers. This adapter does not
construct a query from a bare execute equation or numeric entry data.

## Remaining boundary

This component does not prove retained-used nested-Mu reconstruction
congruence or equality between a body callback and an ordinary callback.
It does not eliminate native `compileMu` child requests back to both input
operands. It does not automatically turn a Head epsilon origin into one
original ordinary-body row: the returned node/union reconstruction receipt
is the next input for that extraction. It gives no new guard-only class
origin, ancestor-owner separation, fresh-call bound, or outer termination.
It does not prove arbitrary open Head completion. Existing supported-open
Head producers remain separate.

The checked query adapter relies on `PhysicalTraceCompletion.Trace` inside
its actual receipt. That trace includes per-step physical `Inputs`. The
proof does not infer these checks from host execution or a bare worker
result. Native writer History and Mu publication History are different
objects. This component retains the former captured native writer; it does
not infer a Mu publication's callback growth from weak publication history.

## Constructed checks

The fixture builds an original container with a productive raw Mu and a
mixed union containing that Mu and a leaf. The Mu's stored ordinary body
is open and has a pair row with a full equality-bearing constraint and two
ordered child positions. Initial `Ready`, availability, and closedness are
derived from the source build. The new `complete` constructs its actual
Head. A literal reader equation and `Head.unique` identify the exact Head
and full returned heap. The typed public witness asserts a selected pair
row, its full original constraint, arity two, and `HeadRows`. This prevents
a vacuous empty-output test.

The second check feeds the original union to another own `complete` at the
first Head's exact returned heap. It aligns the actual warm Head and whole
heap and derives an original member index and origin for the same positive
pair row. It does not assume a later heap, Head graph, row relation, or
completion premise. The two final public statements use private checked
witnesses with exact explicit public types. The query adapter has a full
imported proof check; this component adds no separate native query fixture.

## Validation

The selected production check is `recursive-head-direct-4`: terminal zero
and genuinely zero log bytes. The canonical target is
`recursive-head-canonical-1`: terminal zero, 1424 jobs. Its only warning is
the unchanged imported `InternedFreshOrdinaryClosedCompletion` warning.
The owned source is strict-clean. The public group checks all six exported
heads with `#check @`, full declaration printing, and axiom printing.
All final printer sources set `linter.all` and the seven required print
options. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.

Earlier failed immutable attempts remain. Direct checks 1 through 3 failed
at name resolution, explicit index types, and equality orientation. Kernel
checks 1 through 3 failed at constructor witnesses and binder annotations.
The final kernel uses computed constructor tags before it selects the
literal existential witnesses. These failures do not show a counterexample
or an implementation defect. All actual read and source equations remain
in the checked private witnesses.

Each run executes its own immutable absolute source snapshot with the
pinned Lean 4.34.1 toolchain and `-Dlinter.all=true`. The inner worker reads
its effective cgroup limits: MemoryMax and MemoryHigh are 4294967296 bytes,
and MemorySwapMax is zero. The component does not alter old production,
old evidence, Haskell, Audit, authority documents, or Git state.
