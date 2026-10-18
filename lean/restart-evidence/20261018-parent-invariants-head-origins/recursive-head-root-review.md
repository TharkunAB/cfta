# Independent class-fold guard-origin review

Reviewed on 2026-10-18 at 02:13 CEST. This review is read-only. No Lean build or production edit was made for this review.

Reviewed source: `lean/MicroCFTA/SourceCurrentClassFoldGuardOrigins.lean`.
SHA256: `2b670c1f209de48ab4b4cbebc743ae8ccb8cb850851a5d6cbcfcc3c347169d0c`.
The source matches `class-guard-direct-11.source.lean`. Its recorded exit code is zero. Its log has zero bytes. Root owns canonical and public validation. Canonical attempt 2 was not complete when this review was written.

## Result

No material logical defect was found in the reviewed statements or proof composition. The public results derive guard sources from actual annotated executions and initial invariants. They do not take a final guard-origin classification, a final native writer, or a final Head origin as an input.

## Checked composition

- `node` handles actual leaf, empty, ordinary, and recursive edit constructors. Ordinary rebuilding uses `node_survivor` to recover an actual original row. This step preserves equality of the complete `Guard`, including its raw constraint and formula fields. It does not substitute an effective-own class set.
- The leaf branch derives its `LeafSource` from actual leaf reads and initial native history. The imported query-origin producer retains its checked-trace boundary. The recursive branch derives local closedness from the selected `Safe` path and `HasLeaf`. It constructs a Head origin receipt and uses Head uniqueness to align that receipt with the actual Head event. Unrelated open children need not be closed.
- `children` follows the literal ordered selected/unselected scan. Each output forest index maps to the same input forest index. For a later selected position, the proof obtains intermediate Ready, availability, memo validity, and history from the actual earlier node read. The singleton child scan used for history transport has that same literal node call and endpoint.
- `list` retains the actual list edit. A list-root leaf is the source identity case. A below edit delegates to the indexed child scan.
- `class_sources` derives the initial shared state and compiled edit support from coherent active records, selected path domains, and the actual class read. Its captured original forest is the forest supplied to that class occurrence.
- `fold` follows the source right fold. The tail executes first. The head receives the tail's exact returned forest, checked state, merge memo, and global memos. The proof derives the intermediate receipt and history from actual tail reads. A head input source is traced backward through that same tail at the same forest index. A new head event remains indexed by the literal head graph.
- `pass` handles final empty propagation. A selected returned row rules out the branch that erases every value. The proof therefore derives propagation identity and recovers the exact underlying full fold and its reads. This is a conditional result about surviving rows. It does not assert that every pass has a row.

## Exact scope and residuals

The result classifies complete guard occurrences. `Original` records an input row with an equal complete guard. The event constructors retain an event inside the exact edit/class/fold graph and the same forest index. They do not record a row-survival chain through every later class. They also do not assert equality of complete rows, child records, row order, or row multiplicity across classes. Ordinary row normalization can change these properties.

The guard equality in a tail event does not imply that the same physical row survived the head. The proof needs only a guard occurrence with that field. The event's actual graph remains available for a later, stronger lineage proof.

Leaf events retain the existing `RowOrigin` residual alternatives. Head events retain `HeadRows`. Neither result removes the retained-used/nested-Mu reconstruction boundary or flattens every epsilon origin into one original stored-body row. The imported checked native trace includes its per-step physical input checks. This review does not infer such a trace from a bare executor equation.

The public theorems consume actual `Reads` graphs. They verify completed executions; they do not construct a new initial class-pass completion or a numeric bound. They add no finite Cap, whole-forest closedness, future callback, ancestor-owner separation, fresh-call bound, or general outer termination claim.

## Source pins inspected

| Source | SHA256 |
| --- | --- |
| `SourceCurrentAllocatedSharedEditGraph.lean` | `18dcc2fa70e0eb95731fd19607e730664ba031949099de52e9ab1949f623d629` |
| `SourceCurrentSharedEditRowLineage.lean` | `4b02b1748d11f0e5eb19cdd1f4da1f7dd44cfb7164a77c509b560b01d347d28c` |
| `SourceCurrentParentNativeHistory.lean` | `3c88c79958b914299db33ca5875f7795c3e48da99febb56eb6c17377ef1bac64` |
| `SourceCurrentAllocatedClassPass.lean` | `2a0b66d819f2f559f452d7206e6cbdeeb2dfe3e4494d26fd9286f6c1a84299cc` |
| `SourceCurrentEditDomains.lean` | `bb5304bec867617f0d8314b905b35600b464555347ffdc0a5d26d7b96af0aacb` |
| `SourceCurrentNativeQueryRowOrigins.lean` | `93af295d449b1bdf0b35613a3e45597adb4a4086a7d20ce5a70eee1502fa7ec3` |
| `SourceCurrentRecursiveHeadRowOrigins.lean` | `163ea355c8a595b9e53f194266c77dc30749acb48a71bed2c89fc1e6fb2f9c12` |
