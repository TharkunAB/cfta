# Indexed source row child calls

Checked on 2026-10-20 at 16:41 CEST.

The prototype has one public theorem, `MicroCFTA.SourceCurrentIndexedRowCallChildren.indexed_child`. The source hash is `b25200251338bc2d2e71440079297bfdde29ff21160d17071a03239ce3ab56ca`.

The theorem takes the original joint `SourceCurrentConstrainedCapSourceHistory.Context`, one actual `StoredMuRetainedAlignment.RowCall`, and a lookup at `childIndex` in that call's output children. It derives the original child syntax at the SAME index. It also derives the returned-value lookup at that index, the exact ordered `buildMany` prefix, the adjacent child `build`, and the exact ordered suffix. The child entry has the joint context. The theorem derives physical `Grows` and issued-name `Extends` from the original row entry to that child entry.

The row prefix is `call.earlier`. The selected child prefix is extracted from `call.called` by induction over the actual ordered source list. Each successful earlier child preserves the joint context. `call.children_eq` aligns the physical output lookup with the returned ordered values. The proof does not identify a canonical node row index with the original row source index. It does not use an encoded `ChildTrace`.

The size conclusion concerns the original child syntax and the enclosing original `Syntax.node expressions`. Full statement readback confirms that both symbol and guard use `instSizeOfDefault`. This is the generic structural syntax measure. It is not the default concrete `Nat` or `Bool` payload measure, and it is not a bound on constructed values or recursive calls.

No `raw.free` condition is present. Closed intermediate source nodes and open source nodes use the same endpoint. No `Ready` heap, later completion, desired ancestry, native history, or new `Reached` premise is present. Both forward growth conclusions come from the actual source prefixes and their verified effects. The proof does not infer publication history, native history, or an original binding from growth.

This endpoint supplies the missing ordered source-child call for the node arm of `BuildStructuralRowOrigins.SourceRow`. A later composition can traverse the actual `SourceRow.union` receipts and stop at this node arm or the explicit capture/binder alternatives. That composition remains separate. No same-leaf union descent, current-callback/earlier-writer identity, global renewal bound, or Haskell refinement is proved here.

## Validation

`row-child-direct-3` completed with exit code 0 and a literal zero-byte log. `row-child-public-1` completed with exit code 0. The hardened checker accepts the full one-head statement/proof/axiom group. All eight print options are present. The proof has no omitted terms or print errors. Its axioms are limited to the three standard permitted axioms.

Four Lean jobs are retained. The first two failed because the local identifier `prefix` is reserved. The selected third direct attempt and the first public readback passed. No job timed out or exceeded the memory cap. Every job ran under the pinned Lean 4.34.1 binary with `memory.max = memory.high = 4294967296`, `memory.swap.max = 0`, and a five-minute wrapper limit. Recorded peaks were 147, 153, 154, and 166 MiB. No canonical build or constructed fixture was run. Counts are one new public pair, zero constructed pairs, and zero auxiliary pairs.

All authored files and job evidence are isolated in this directory. The repository files in `inputs/` are byte copies of read-only source dependencies and prior art. The manifest pins every owned source, helper, attempt, receipt, log, input copy, and this review. The standalone verifier checks the portable copies. Its optional `--live-root` check also checks those copies against the repository paths.
