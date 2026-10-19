# Actual recursive observation source handoff

Checked on 2026-10-19 at 12:14 CEST.
The component owns `SourceCurrentRecursiveObservationReadOrigins.lean` and one public theorem, `project_read`.
It owns no constructed theorem.

## Actual inputs and result

The theorem consumes an actual Project from a recursive needle, its exact selected Read Spine, initial SemanticReady, costs and availability, and the terminal reader's SemanticReady and forward Keeps.
The projection input can be open.
The theorem requires no changed-input gate, closedness, future completion, desired source law, or whole-event projection.

At an empty residual, the actual Project is the root projection.
Forward Keeps supplies the recursive value's availability at the terminal reader.
The actual completed Read gives `Origin readAfter [needle] row` for the same complete selected row.
The view is the actual Read return heap.

At a nonempty residual, the theorem retains the actual recursive Head and remaining Project.
The Head's actual completed row read and makeNode prove that its exposed result is ordinary.
The remaining selected Spine therefore has an ordinary ProjectionFrame.
That frame retains the selected canonical Head row, its exact row index, the signed child lookup, earlier and later row projections, the actual child Project, the selected operand Read and its internal read index, and the child's remaining Spine.
The final selected row remains the same full row in that Spine.
Its internal position can differ from the outer Read position.

Actual makeNode readback proves that this canonical Head row is present in the actual Head read's row list.
The result retains that separate raw index and the complete Head read and constructor equations.
The actual read-origin theorem then gives `Origin headAfter [needle] frame.sourceRow`.
The result retains the complete Head row, including symbol, guard and ordered children.
Its signed lookup derives a natural child index and the exact list selection.
HEq binds the returned Head and body Project to the exact supplied Project.

The selected Head row can differ from the final selected row.
The theorem does not assert an epsilon Origin for a deep final row at the recursive root.
It does not replace the actual remaining projection by a projection of an earlier event value.
It supplies no initial query-operand ancestry, source mass bound, general progress measure or termination result.

## Reused producers

`SourceCurrentClassObservationSpines.ProjectionFrame` supplies the full existing ordinary continuation.
The new theorem does not introduce a second frame type.
`SourceEqualityProjectionCosts.read_effects` supplies the actual Head read's semantic, cost and resident-row facts.
`SourceEqualityOpenOrdinaryHead.node` and the physical makeNode readback retain the actual canonical Head row.
`MergedFreshOrdinaryExposureOrigins.nodeEdges_origins` supplies the two actual reader-relative origins.
The older HeadChainRows, HeadNodeRows and HeadUnionRows actual producers require closedness and do not replace this open-input adapter.

## Selected evidence

Final production SHA256 is `9cb1958944b2730d0a85ddc83a7ee21b5c12a895782d10c849d44f19a123cb7a`.
Selected `origin-direct-4` terminates with code zero and its log has literally zero bytes.
Its source snapshot is identical to production.
Selected `origin-canonical-1` terminates successfully and builds the canonical interface.
Its only warning is the unchanged dependency warning in `InternedFreshOrdinaryClosedCompletion.lean:24:5`.
The new module has no warning.

Selected `origin-public-1` prints the explicit type, full proof and axiom report for the sole public theorem.
Its 8750140-byte log passes the hardened read-only checks for all eight settings, no omissions and only the three standard axioms.
No proof alias hides a separate constructed premise.

All five entered Lean jobs record memory.max = memory.high = 4294967296 and memory.swap.max = 0 under the 4 GiB / 5 minute wrapper.
The component pins an immutable five-row peaks snapshot.
It does not pin mutable root or other-owner metadata.

## Preserved attempts

`origin-direct-1` did not enter Lean.
The filesystem sandbox blocked the local systemd user bus before the capped worker ran.
Its failed wrapper receipt, raw log and source snapshot remain preserved.
The authorized check was then run through the same capped worker with access to the local bus.

`origin-direct-2` reached Lean and failed on inferred index types, dotted constructor inference and dependent-case names.
It also reported unused helper instances.
The helpers were moved before the instance scope.
`origin-direct-3` failed only on names already unified by dependent case elimination.
`origin-direct-4` checks the corrected proof with no output.
The canonical build and public proof check are the fourth and fifth entered Lean jobs.
No earlier attempt is selected or overwritten.

This component changes no older source, Audit import, documentation authority, Haskell file, or frozen evidence component.
