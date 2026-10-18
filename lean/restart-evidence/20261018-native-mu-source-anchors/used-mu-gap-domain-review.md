# Open-domain boundary for query source ancestry

Date: 2026-10-18 CEST.
This supplement preserves `used-mu-gap-review.md` and its original manifest.
It adds a source audit. It adds no theorem or execution result.

## Closed roots do not imply closed internal requests

`SourceRecursiveIntersectionCompile.compileMu` extends the domain and then
requests `body left` and `body right` at that entered domain (lines 28–33).
Those stored bodies can contain references to their enclosing binders.
They can therefore be open when both initial Mu operands are closed.
A recursive source-row proof must follow these actual body requests.
It cannot repeatedly apply a closed-operands endpoint without a new argument.

`SourceCurrentNativeMuWriterSourceRows.MuRow` retains that exact entered
body request and its checked trace. Its `Anchor` selects a `RowAt` occurrence
in the actual generated body result. That body result need not be a row
occurrence of an initial query operand. The theorem preserves full fields
within that generated-body rebinding step. A native ordinary join instead
needs paired operand rows and its actual conjoined guard.

## An open reference can still have a native memo key

`IntersectionFlatMemoKey.input` accepts `.ref (.interned identity)`
(lines 15–21). It rejects the other reference variants.
Thus an actual bound `RecInt` reference can be keyable despite being open.
Intersection and uninterned placeholders bypass this source-key layer.
Key presence and machine-width safety are separate properties.

`SourceRecursiveIntersectionThunks.lookupNode` uses the direct branch only
when the complete `requestKey` is `none` (lines 89–95).
`SourceCurrentSharedLeafNativeLineage.Origin` already preserves the exact
successful split: a direct actual `compileNode` trace, or a returned cell
with its actual protected writer (lines 43–48).
It does not classify the source of every ordinary result row.

`SourceCurrentNativeQueryRowOrigins.keyable` uses closedness to prove key
presence (lines 78–80). `forwarded_returned` uses it to eliminate the direct
alternative (lines 228–240). `normalize` retains closedness through swap
and reset (lines 242–275). The new `NativeQueryMuSourceRows.request` keeps
both closed-operands premises. These are explicit scope conditions.

## Exact next provenance obligation

A domain-aware row-origin induction must preserve the successful direct
trace or returned-writer alternative at each actual request.
For a reference branch it must expose the exact domain-membership test,
actual `read` result, bound value, ordered forwarded request and its trace.
`compileReference` states these operations at lines 37–43.
`compileNode` only sends an interned reference to that branch (lines 76–81).
The domain/available-input invariant must justify the read. Closedness of
the original roots cannot replace that invariant at internal requests.

The Haskell source has the corresponding Mu environment extension and body
calls at `Interned/Operations.hs:506–508,529–535`. It resolves `RecInt`
through `idFree` at lines 513–514 and 537–541.
This comparison identifies the proof boundary. It does not establish a
new executable defect or general Haskell correspondence.

This obligation is additional to retained used-Mu alignment.
The current closed-root query integrations are valid within their stated
scope. They do not discharge this open-domain induction.
