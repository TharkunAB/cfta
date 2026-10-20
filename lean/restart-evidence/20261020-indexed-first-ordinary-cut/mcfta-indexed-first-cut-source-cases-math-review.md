# Indexed first-cut source cases: independent mathematical review

Reviewed on 2026-10-20 at 16:47 CEST. This review uses the current source files. It runs no Lean job and makes no repository edit.

No material mathematical issue was found in the 37-line `SourceCurrentIndexedLeafSourceRows.lean`. Its source SHA-256 is `8a1d9dcbc991b1127647518521f85f2a61140b12723c881fc23ff58f0b57ec62`. The reviewed Cut source SHA-256 is `98e3f0059871cf60a9fa68b976c1975a7cf4a791e612d351740de020d7aa1deb`.

The public `source_cases` theorem takes one actual completed source build, its original joint Context, and an exact lookup of `leaf` at `index` in `leaves raw`. It also takes a structural `RowAt leaf row`. It does not take a desired source-origin premise, a future completion, a Ready heap, or an assumed binding ancestry.

The proof passes the SAME `raw`, `index`, `leaf`, lookup, `row`, and `RowAt` to `IndexedFirstOrdinaryCut.split`. In the direct arm, the resulting `RowAt raw row` is used verbatim by `build_row_origin` with the SAME expression, inputs, before heap, returned raw value, after heap, Context, and actual call. The result is `SourceRow` for that exact selected row. No row is substituted by equal fields alone.

In the cut arm, the proof retains the SAME `Cut raw index leaf parentRow childIndex child inner` witness returned by `split`. Its `facts.1` supplies `RowAt raw parentRow`. The proof applies `build_row_origin` to that exact parentRow and the SAME original completed source call. Thus the cut's selected child index and inner leaf index remain attached to the source-classified parent row. `Cut.facts` also derives the exact parent child lookup and exact inner leaf lookup. It does not change either index. The theorem does not assert that parentRow equals the selected leaf's row.

## Foundation checks

`leaves` first stops at every value whose free list is empty. For an open node, Cut records the canonical physical row position, the physical child position, and both preceding leaf counts. For an open union it records the actual member index and preceding member leaf count. For an open Mu it retains the SAME index while following its literal stored body. These constructors record a first ordinary-child crossing. They do not unfold Mu in an observation reader.

`split` handles the closed shortcut by deriving index zero and exact leaf equality. Its open-node case derives both offsets by ordered flat-list lookup. Its union and Mu cases recurse over strictly smaller literal values. The source-cases theorem adds actual source execution evidence to that pure split. It does not change the split or infer a source call from a leaf equality alone.

`SourceRow.node` keeps the canonical output row index separate from the original source row index. Its `RowCall.output = row` is equality of the complete row. Its actual child build and row prefix/suffix remain attached to that receipt. `SourceRow.union` retains the exact original member index, adjacent states, call, suffix, Context and nested source classification. It does not assert same-leaf membership in an original source member. `SourceRow.capture` stops at the exact lexical input slot. `SourceRow.binder` stops at the exact selected complete Mu payload, current probe/request equations, actual finish equation and structural row in the selected body. The selected stored body can come from an earlier cache writer with different syntax. This endpoint does not replace that body by the current raw callback.

## Exact scope and remaining work

This is structural row ancestry from an actual completed source build. It covers smart binder cleanup and closed intermediate source values through the existing SourceRow producer. It is not an observational epsilon Origin, a MuRead continuation, a selected original binding, or a global renewal/termination bound. Context supplies the existing heap and lexical invariants; it does not assume the desired SourceRow conclusion.

The cut arm still needs a general source-child-call composition for the parentRow. The separate indexed RowCall extractor prototype is NEXT work and is not imported by this checkpoint. A later proof can traverse actual SourceRow.union receipts and derive an ordered child source call at the node arm. Capture and binder arms need their explicit original-input or same-writer provenance steps. The cut's normalized value-member positions must remain distinct from original source-union member indices. No native history, empty native captures, current-callback/earlier-writer identity, or Haskell refinement follows from this theorem.

Counts: one independently reviewed new public theorem and three reviewed Cut heads; zero owned proof pairs, zero constructed pairs, and zero new Lean jobs. The existing SourceRow foundation was reread for this composition. This note does not replace root-owned strict, canonical, full-print, or Audit receipts.
