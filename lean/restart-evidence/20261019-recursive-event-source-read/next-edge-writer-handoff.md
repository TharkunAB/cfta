# Next native ordinary-child memo handoff

Read-only audit: 2026-10-19 12:54 CEST.
No production file changed. No new Lean process ran for this audit.
The proposed theorem below is not yet checked.

## Exact loss of information

`SourceCurrentNativeReaderRowLineage.rows_child` derives the actual selected
edge call and its returned cell. Lines 124–127 compose the actual row-walk
suffix, parent makeNode return, and supplied parent retention into the
captured checked reader `q`. This already proves retention from the actual
edge-call return to `q`.

Line 128 invokes `SourceCurrentNativeEdgeWriterGrowth.History.writers`.
That theorem finds the edge's earlier captured writer. Its `Written`
receipt, lines 30–39, retains the captured Good entry, owner, edge-body
trace, protected finish and both heap-growth facts. It omits retention of
native returned cells from that SAME captured edge-body return to `q`.

`NativeWriterChildOrigins.live` inverts that earlier edge body. Its accepted
branch retains the actual ordered child Walk and later makeEdge call.
`child` selects the exact child call, its prefix and its suffix, but returns
only child Trace, Good states and heap growth. A field is lost before these
inversions, rather than requiring an independent history at the child entry.

## Minimal new chronological foundation

Add an edge analogue of `SourceCurrentNativeWriterReadyRetention.Written`.
It must take a native reader state, and add this field INSIDE the existing
captured edge-body existential:

```
Retained capturedEdgeBodyReturn.native q.native
```

The proposed producer is:

```
History.edge_writers
  (history : History q)
  (cell : q.native.edges.cells handle = some <request,returned row>)
  : EdgeWritten q.native handle request row
```

`EdgeWritten` denotes the proposed stronger receipt. It is not an existing
public declaration. Its before, after, fuel, owner and body trace must be
the SAME witnesses used by its retention field. A weak `Written` followed
by an unrelated existential retained trace is insufficient. The protected
finish does not itself supply the missing interval into `q`.

The existing `History` is sufficient to derive this receipt. Its initial
case has no returned cells. Its physical-advance case preserves both memo
families and uses `SourceEqualityNativeDemandMemo.advance_retained`. Its
completed-trace case can use the same actual prefix induction as the node
receipt, with edge owners and finishes. No new user premise or past/future
successful execution is needed.

Adapt these concrete node-receipt helpers in the new module:

- `NativeWriterReadyRetention.trace_retained` is already public.
- The private `later` and `recorded_change` compose growth and retention.
- The private `recorded_lookup`, `recorded_demand` and `recorded_finish`
  handle cache changes and retain the same captured writer.
- The private `preserves` computes `nextCells` from
  `SourceEqualityNativeDemandMemo.step_preserves`. It stamps a new captured
  writer with `Retained.refl`, then extends it through its actual finish
  and continuation.
- `NativeWriterReadyRetention.writers` supplies the final History induction
  pattern. The edge version selects `edges.cells` and uses finishEdge.

The current `NativeWriterReadyRetention.edge_writers` helper returns the
older weak edge receipt. It therefore does not already discharge this
obligation. Frozen earlier files should remain unchanged.

## Exact child retention and reader provenance

Repeat the live-edge inversion with the stronger SAME-writer receipt.
Keep the returned child Walk and the makeEdge trace from that inversion.
For the selected child, compose:

```
Retained childReturn.native childWalkEnd.native
Retained childWalkEnd.native capturedEdgeBodyReturn.native
Retained capturedEdgeBodyReturn.native q.native
```

The first fact follows from `trace_retained` on the actual child-Walk
suffix, using Good at that child return. The second follows from
`trace_retained` on the actual makeEdge call. The third is the stronger
edge receipt's new field. Their composition gives the desired exact child
return retention. The actual parent row-walk and makeNode suffixes connect
the edge call's completed result to `q`; they are already available in the
row-level proof.

Apply `SourceCurrentNativeReferenceOrigins.forwarded` with History at `q`,
Good at the actual child entry, the actual child Trace and the derived
retention. This returns `Forwarded q childRequest childBefore childAfter
childResult`. It requires no History at that active internal child entry.

The stronger row-level target can keep the existing indexed input rows,
full symbol/guard conjunction, exact paired child Trace and heap growth,
and add:

```
Retained childAfter.native q.native
Forwarded q childRequest childBefore childAfter childResult
```

Call this proposed theorem `rows_child_forwarded`. Then an ordinary-node
adapter can preserve the two strict source-child mass bounds already
proved in `NativeOriginViewBranches.ordinary`.

## A stronger returned-cell consequence

For an actual surviving ordinary row, `rows_child` already derives
`Value.empty` absent from every returned child position. The selected
child is therefore nonempty. If its Forwarded receipt used the unresolved
direct arm, `NativeRowKeyable.unkeyed_empty` would make that actual child
result literal Empty. This contradicts the survivor fact.

Thus a proposed `rows_child_returned` can additionally derive the exact
child returned cell and `NativeWriterReadyRetention.Written` at `q`.
This consequence needs no additional child Origin, closedness, positivity
or semantic result law. It uses the actual surviving row and successful
child call. It remains a proposed composition, not a new checked theorem.

## Cold, warm and later physical views

A cold edge call exposes its current body and actual child suffix. For a
warm edge hit, the current call has no child Walk. The causal History at
`q` must recover the earlier writer WITH its retained native suffix. This
is why returning the current cold-call retention alone is incomplete.
Both cold and warm node paths are already covered by the stronger node
writer receipt and actual trace-retention lemmas.

The new retention must end at the actual captured checked reader `q`.
It must not end at a constructed checked state over a later physical view.
The separate `PathOrigin` view remains unchanged. Once the child's exact
returned cell is known at `q`, its same returned value and actual remaining
path can enter the next native source step. No arbitrary Origin transport
or whole-event Project is needed.

This repairs the ordinary child native-provenance interface. It does not
identify selected stored Mu winners with current callbacks, prove initial
operand ancestry, give a global renewal measure, or establish termination.
