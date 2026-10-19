# Class observation edit-spine review

Reviewed 2026-10-19 01:58 CEST. No material issue remains in the final source.
The full 990-line source, its final public wrapper, and its selected strict receipt were read.
This is an independent source and strict-receipt review. It makes no canonical or full-printer claim.
No Lean job or production edit was made by this review.

## Corrections made during review

The initial ordinary constructors had separate outer-spine and frame witnesses.
The frame did not name the outer `Project`, `Read`, or selected position.
The final `ProjectionFrame` is indexed by all three.
It also retains `exactProject`, the exact observed lookup, and its canonical lookup.
The ordinary constructors now use that frame directly.

The initial constructors also allowed an independently chosen child index with an equal child value.
Repeated equal children could therefore obscure which physical slot was followed.
Both final constructors require `index = Int.ofNat childIndex`.
The producer derives this equation from the successful signed lookup.
These were occurrence-contract corrections. No checked language or implementation counterexample was claimed.

## Final causal connection

The unchanged branch retains the same physical child position, the absent edit lookup, and its actual ordered `Slice`.
The selected branch retains the same position, its literal child edit, its real earlier and later child calls, and their `ChildrenReads`.
Its recursive witness uses exactly `frame.call`, `frame.operandRead`, and `frame.readIndex`.
The selected parent row is connected to the raw reconstruction and original row by the reconstruction receipt.
Projection result position, canonical row position, and raw reconstruction position remain distinct.

The leaf cut retains the actual leaf receipt, native history, and the complete remaining projection/read of that leaf result.
The Head cut retains its actual Head, global effect, and recursive body edit/read.
Its remaining observation starts from the body return. It does not observe an unchanged exposed input.
An event in another sibling cannot be selected by these corrected ordinary lifts.

The raw union index still denotes an equal full-row preimage.
It is not asserted to equal the offset of the selected operand's row interval.
This agrees with the reviewed projection-spine contract.

## Support and public endpoint

The private induction derives selected edit-prefix and edit-suffix effects from actual read graphs.
It derives child projection and operand-read support from their actual projection/read prefixes and suffixes.
Growth from a child edit return to its later projection entry follows those actual effects.
`Keeps` from the child projection return to its operand-read entry follows the projection suffix and union-read prefix.
The causal guard heap is restricted backwards from the explicitly supported final reader along these forward growth chains.
It is not inferred forwards from growth alone.

The public `node` wrapper starts projection at the exact edit-return heap.
It derives that heap's semantic readiness, cost heap, and result availability with `node_effects`.
It constructs original path safety from the original false gate, then transports that safety through the supplied Required origin.
It does not require a false gate on the prepared or edited value.
The source alternative retains the same-path ordinary `Route` and full `RowOrigin` fields.
It does not claim unchanged children or `All₂ Required Origin` across native edits.

`Reconstruction` repackages the data and facts already present in `ClassFoldRowOrigins.Rebuild`.
The private adapter invokes `rebuild`; it does not repeat physical preservation induction.
A data record permits the dependent field projections used by the spine constructors.
This is representation duplication, not another mathematical producer or an extra result law.

## Selected source and receipt pins

The strict job is terminal 0 with a literal zero-byte log.
Its recorded maximum and high are both 4294967296 bytes, swap is zero, and its wrapper uses 4G/5m.
Canonical and full public checks were still parent-owned pending work when this source review froze.

| File | SHA256 |
|---|---|
| `lean/MicroCFTA/SourceCurrentClassObservationSpines.lean` | `ebc2c41f025b4803e58c5212087a6799117c7ae8807771c36a89e254f3cf0cb2` |
| `observation-spine-direct-11.source.lean` | `ebc2c41f025b4803e58c5212087a6799117c7ae8807771c36a89e254f3cf0cb2` |
| `observation-spine-direct-11.json` | `9e7eb015903a6f6125e745606a80c23d78d693197f8ba5e3619694362d419823` |
| `observation-spine-direct-11.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `observation-spine-direct-11.limits.json` | `408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3` |
| `lean/MicroCFTA/SourceCurrentClassFoldRowOrigins.lean` | `d57ecf4371ed53c17ca0f64feb30994764612cac51483eb36a207a0f5fa4faab` |
| `lean/MicroCFTA/SourceCurrentProjectionReadSpine.lean` | `b58d94bcae9b63cffd8b9193d0d795609efbf8206adfe14c62f0dbb5e1282499` |
| `lean/MicroCFTA/SourceCurrentSharedEditChildLineage.lean` | `822fd3d96648267efd014547599b94530b9ce98e6d3c615831a94f8c2bfca4d0` |
| `lean/MicroCFTA/SourceCurrentRequiredProjectionOrigins.lean` | `ebf430e8c217d2f6083ea23447ae56df5f4ede03a67341d407e002eca2abdc67` |

Unqualified receipt names in this table refer to the containing evidence directory.
This review owns zero new Lean runs and zero proof pairs.
