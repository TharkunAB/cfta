# Immutable frame ledger interface

The exact source declaration is IdentityActualFrameLedger in the appended
source. Its parameters are formulas, solver, root, metadata and uv. Its
indices are:

    actualFrame, activeOriginalCaller, activeBeforeCache, activeFullInputs

The captured constructor indexes the active scope by:

    capturedCaller, actualOwnCache, actualStagedPairs

It retains the actual captured row-entry Packet/query, Ready/stored/IncomingAvoid
for uv, and the literal CachedOwn.prepare singleton. This supplies the real
captured entry context after any later nested source entry.

The selected constructor indexes the NEW active scope by:

    rowCaller, rowOwnCache, actualInnerStagedPairs

It retains these immutable fields:

- parent frame and ancestor ledger with the parent scope's original/before/inputs.
- parent completed prefix and remaining tuple inputs.
- incoming ordinary input and its bucket.
- actual row-entry caller/query, before cache and own cache.
- selected row/residual, parent height/count/bound, captured mass and row seed.
- actual row-entry inventory/memos, Packet/query and outer full TupleInputs.
- incoming head membership in the full outer inputs.
- literal own receipt.
- exact point.Inputs snapshot for incoming::rest at that row entry.

The snapshot's count is the remaining parent count bound; its input capacity
is count+1, so rest.length≤count follows. It retains all parent input ranks and
bucket/vars/pending facts at the real row-entry cache. Its Shapes/Keeps refer
to the original root captured heap, not a heap computed after native effects.

The selected own producer also returns outer TupleInputs at rowOwn. It returns
inner SourceCurrent with the genuine new local scope. Its parent ledger is
copied unchanged. Root's selected-return case can derive actual head ChildInputs
from the immutable entry Packet/receipt and current full inner TupleInputs.
It can then derive the true remaining parent inputs using child_then_tuple_inputs,
compose Keeps, and use the checked actual handoff for current native resource
padding/reservation. It must not cancel a root Post to obtain the local Post.

The current ancestor histories after further inner execution are not stored
as future promises. They must be derived from the immutable ledger snapshots
and the actual current inner TupleInputs, using tuple_inputs_after_nested_prefix
at each selected ancestor. That recursive producer and the complete joint task
induction remain OPEN.
