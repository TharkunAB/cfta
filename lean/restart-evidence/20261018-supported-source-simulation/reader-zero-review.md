# Independent review: zero stored-plan depth reader support

Date: 2026-10-18 13:53 CEST. Read-only review. No new Lean execution.

## Pins and finding

Reviewed production source:
`lean/MicroCFTA/SourceCurrentZeroDepthReaderSupport.lean`, SHA-256
`5f09e107b1d1acb269e72a4fb3c5456145cc8dfe0454fa2b2236591df00cff7f`.
No material issue was found.

The two public declarations are `warm` and `prepare`. Existing selected
receipts are `zero-depth-support-direct-2`,
`zero-depth-support-canonical-1`, and `zero-depth-support-public-1`.
Their recorded exit codes are zero. The strict log is literally zero bytes.
The imported probe prints both complete heads with all required options.
It contains no elision, warning, error, printer failure, or `sorryAx`.
Only standard axioms occur. The existing inner-limit records show effective
memory limits 4294967296/4294967296/0 under the five-minute capped wrapper.
This review reuses those receipts and does not count them again.

## Mathematical scope

`valueDepth` first tests the physical free-name list. Closed records are
opaque depth-zero stored captures. An open literal Mu has depth one plus
its stored body's plan depth. Therefore a Mu at depth zero must be closed.
The private `mu_closed` proof uses exactly those definition branches.
It does not infer closure from ordinary semantic language equivalence.

`warm` takes initial Ready and existing closed-value WarmSupport. It derives
WarmSupport for every available value with zero stored-plan binder depth.
For ordinary nodes and unions, `ordinary_child_le` uses the actual coherent
resident payload and the exact original children. Thus each exposed member
or ordered row child remains available and has depth zero. A Mu in this
support is closed. Its epsilon closure and settled actual unfolding come
from the existing closed support. Closed results have depth zero by
`closed_zero`. Empty, reference, node, and union unfolding is the literal
pure operation; no recursive completion is assumed in those cases.

`prepare` starts from Ready alone. Existing closed preparation constructs
a finite actual `Preparation`, final Keeps, and closed support. The new
proof applies `warm` at that produced Ready heap. It does not supply final
WarmSupport or final completion as an input.

The support can include open ordinary nodes, unions, and references, with
closed Mu values below them. It excludes arbitrary open Mu values. It is
not a theorem that every available value is settled. The open-depth
restriction remains exact and explicit.

## Limits

The new theorem does not compare observations in the original cold reader
with observations in the prepared reader. Existing support replay can be
used only after its actual WarmSupport premises are established. The
new theorem does not infer a completed native or outer computation,
retained-binder correspondence, source occurrence lineage, or an arbitrary
open-Mu warm support invariant.

The root owner is checking a separate source-built open node/union/closed
Mu integration. This review pins the final general source and its existing
strict/canonical/public receipts. It neither changes nor double-counts the
root's constructed integration or public group.
