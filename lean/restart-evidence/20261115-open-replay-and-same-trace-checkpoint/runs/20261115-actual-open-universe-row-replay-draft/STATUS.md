# Actual open universe-row constructor replay

Status: UNCOMPILED candidate. No proof credit is claimed.

The packet has two public targets:

- `original_top_self_body_prefix` derives actual field lookup, ready Top
  conjunction, reached allocation validity and growth, and the literal checked
  child continuation. Its field input is an existing `Origin` receipt for an
  earlier original source-field constructor. It does not assume a future field
  lookup or allocation result.
- `open_row_replay_and_returned_of_children` preserves both existing `Returned`
  laws at every supplied fuel. For actual completion at that same fuel, it
  derives the ordered constructor inputs from the actual smaller child queries.
  It retains the original request, domain, source row, actual allocated prefix,
  full constructor result and exact reached state.

The source is a literal self row with the source Top guard. The domain remains
unrestricted. No closed-domain or `Profile` premise is used. The replacement is
the existing source substitution input map. It replaces the original interned
source name with the literal `repeatedValue (pair cutoffLeft cutoffRight)`.
The two cutoff identities remain separate from the source name. This retains
the off-diagonal body/Mu case. It does not force the diagonal U/U cutoff.

For example, when the source children are `[marker, ref u, ref u]` and the
marker is closed, the source input map gives
`[marker, repeatedValue (pair b u), repeatedValue (pair b u)]`.
For a catalog row with `n` copies of `ref u`, it gives `n` copies of that same
cutoff. The original source order is retained.

Both child hypotheses retain actual prefixes from this same `.edgeBody`
execution. Their child budgets are strictly below the supplied original body
fuel. `childrenReturned` covers every child endpoint. `childrenReplay` identifies
only an actual completed smaller query result. These are intermediate
induction hypotheses. They are not proposed as new original caller contracts.
The packet does not derive the literal cutoff result from an arbitrary open
domain by itself. That smaller child-query law remains to be discharged from
the actual source control and retained Returned laws.

The exact replay conclusion is about the actual ordered constructor inputs:

```text
values = source.children.map (input (replacement (interned u) cutoff))
result = (run (makeEdge source.symbol Top values) actualMiddleHeap).1
```

The result includes every actual edge-cache effect. The packet does not replace
the actual interned result with a proposed resident target row. It does not
assert `result.children = values` without the physical facts which justify
that cache readback. `MergedPhysicalGroupEdges.makeEdge_fields` supplies that
next step when actual smaller child results establish current heap facts and
availability. `ProbeRowReplay.resident_edge_replay` can then recover an exact
already resident target row. Neither future physical facts nor future target
residency is an input premise here.

The older RowTransform, OffDiagonalBody, ProbeRowReplay and CanonicalRowReplay
modules were inspected. Their kernel and constructor replay facts do not prove
this checked-body field/allocation prefix. The candidate uses actual checked
body observation and the existing all-fuel Returned theorem. It does not use
older `compileEdge`, eager execution or a semantic provider.

No compiler, live source edit, Git action, board action or `/tmp` action ran.
No Haskell source changed. No Haskell bug or fix is claimed.
