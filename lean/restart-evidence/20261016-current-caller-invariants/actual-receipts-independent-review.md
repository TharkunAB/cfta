# Independent actual-return and caller-frame review

## Result

No material defect was found in the three reviewed modules. This review does not establish whole-caller termination, semantic correctness of every outer body, or runtime demand correspondence.

## Structural frames

`SourceCurrentAllocatedPartialFrames.Protocol` at line 25 is a physical thunk protocol. It retains literal key links and cell bounds. It does not include a language law or current equality-cache coverage.

`beginNode_owner` and `beginEdge_owner` at lines 104 and 126 derive the evaluating cell at the literal selected handle and its original request key from actual lookup/demand. They do not identify complete request payloads from a key without a separate physical coherence argument.

The private `*_handle_not_running` proofs at lines 173 and 188 use an actual completed Call to contradict a busy observation. The proof does not turn busy into success. The mutual frame proof preserves earlier Running and Returned cells. Its own finished cell was not Running at call entry. The completed graph is explicit; general completion and physical/semantic validity are not conclusions of the frame alone.

## Source read refinement

`SourceCurrentAllocatedPartialSourceReads` defines all eight families over the same frozen raw traces. Only the parent leaf changes to strict `ParentEdgeActual.Reads`. Ordered edge/descendant/tail and descended-child/tail composition is retained. The eight erasures keep the same caller trace, all intermediate return indices, and final global bundle. There is no old-to-strict implication.

The binder branch is a schedule assertion with unchanged global bundle. The header explicitly leaves the general Mu reconstruction `Runs` adapter and runtime forcing open. The proof does not derive physical heap coherence from silent schedule annotations.

## Actual filtered probes

`SourceCurrentAllocatedProbeActual` consumes the same strict stage/local/parent Reads as the actual receipt verifiers. The Scan call is the supplied actual Scan. The required worker proof uses its literal fuel, result, heap, and completed equation. RequiredActual aligns the independently derived required receipt by completed graph uniqueness. It does not align global bundles across different schedules.

At the parent live branch, `local_heap` uses the supplied local Reads and its exact middle state. `mkEdge_heap` then applies at that middle. The supplied `built` equation rewrites the literal constructor pair to the actual final state. The proof does not apply `parent_finite` or replace the parent by another existential completion. Initial ProbeHeap remains explicit.

## External integration

`parent-probe-same-return.lean` kernel-checks `same_parent_return`. It applies ParentEdgeActual.verified and ProbeParent.parent_heap to one supplied strict Read proof. Both conclusions retain the SAME implicit result, checked after-state, saved fourth memo, merge memo, and final three-table bundle. It also derives historical read erasure for that same raw trace.

Two further external kernels preserve an original running node cell through an actual edge Call, and erase a strict outer edge schedule without changing its trace or bundles. Direct Lean terminated 0. The signature and axiom output are in `parent-probe-same-return-1.log`. Only propext, Classical.choice, and Quot.sound occur.

Reviewed source hashes:
- `SourceCurrentAllocatedPartialFrames.lean`: `4b6c2b9f656c7aede31c4fbbdecb82c57ec5be4ee619abe223d40fe04238240e`.
- `SourceCurrentAllocatedPartialSourceReads.lean`: `0303236146b100c2ba3a6352280cf8763af17eb54a190b4e32601d52d7091892`.
- `SourceCurrentAllocatedProbeActual.lean`: `ccd0b2ea922e2792e41b29485380ab3124695025aee642aac8c15e29e21d8b10`.
