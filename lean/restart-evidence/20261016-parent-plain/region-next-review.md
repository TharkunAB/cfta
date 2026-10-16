# Next current Region completion induction

Reviewed at 2026-10-16 15:26 CEST. This is a read-only dependency audit. It does not claim that the eight-family completion induction has been implemented.

## Exact current domain

Reuse `SourceEqualityPartialPlainRegion.Region/Rows/Children` at lines 17–32. Region stops at Mu and union values. Each ordinary row requires `SourceEqualityPhysicalPayload.own guard = .ok (some [])` and Region children. `PhysicalPayload.own` at lines 23–24 reads `SourceCompactGuards.sourceEqualities`, including positive guard extraction. It does not read only `guard.equalities`.

The pure conversion from physical own-empty to effective source-empty must invert `PhysicalPayload.read` and `ClassOrder.recordsOf` at lines 85–90. A nonempty class list creates a nonempty record list or fails. It cannot produce `some []`. No normalization or semantic answer premise is needed for this inversion. The frozen `SourceCurrentAllocatedPartialPlainInputs.own_empty` now proves this exact inversion. Its `rows_member/children_member` transfer the ordered structural domain. This review read the final direct-green source, SHA256 `d9b94b6cea1374c82b2b65bb4efad01328cd85106bec80e16a3db3da01917065`; its canonical build and imported probes belong to required_memos.

`SourceCurrentAllocatedLocalPlain` already derives actual allocated precheck cases from ready stored and inherited values. `complete` returns the original child list or erased slots at the literal precheck state. It needs no child closedness, positive execution bound, native result, or callback. `LocalPlainRanges.resident_ranges` derives the complete reached parent range plan from the current resident field. Its `nil_ranges` proof inverts the actual nil Scan and retained list. It does not assume a future class result.

`SourceCurrentAllocatedParentPlain` is source-frozen at SHA256 `527480a85b9a245b1c6e1048c8eb610940a8da1476a40f58d99092c2552e2524`. Its `Plain request` tests effective own-empty only if raw contradiction is false. `finite` derives stable literal execution, the actual current EdgeBody, strict reads, current receipt, full Post, three-way Shape, and height. Its `done_shape` aligns supplied literal success with that exact finite return. The private shape proof uses the actual local graph/reads, current field load, LocalPlain output shape, and actual MkEdge constructor result. No general parent completion callback, final readiness, or desired result law is supplied. Raw rejection and checked constructor rejection both use the singleton Empty sentinel.

## Warm requests and exact structural transport

`PartialCallSteps.node_start/edge_start` derive current owner input facts, inherited readiness, exact running cells, and stored/candidate key equality. `PartialKeyTransport.available_reference_eq` at lines 118–124 and `InternedEdgeResidency.edge_identity_unique` identify complete immutable operands in the current coherent heap. Apply these equalities to Region, effective own-empty, and child Regions. Equal rank alone is insufficient to transfer Region. The owner inherited payload need not equal the candidate's complete physical record: the induction handles every ready inherited value, and each stored owner already has its own readiness.

`PartialActiveOrder.node_begin_safe/edge_begin_safe` exclude busy and absent observations from current Sound, coherent residency, and ActiveAbove the candidate rank. A ready hit must read the returned certificate of its actual captured owner. The frozen `PlainInputs.edge_ready_shape` now derives the exact ready-hit Shape by reading the initial returned owner, current key link, and coherent resident operand equality. `node_evaluate/edge_evaluate` derive the corresponding started-owner Region facts. They contain no future body premise. Do not replace these facts with a candidate result-law oracle.

`PartialReturnedDomain.Stored` is an additional structural warm-cache invariant. Context and semantic EdgeLaw do not imply it. Cold result tables derive Stored. Its publication/demand/advance/finish laws are now proved. A completion induction must return Stored at every recursive result, in addition to Post. Do not assume it at the next sibling.

## Minimum induction interface

A useful public node endpoint should take only initial current Context, Stored, ready inherited value, available input, Region input, and ActiveAbove its nodeRank. It should construct a result and the same returned full caller with: actual NodeCall, strict NodeCallReads, Checks, Post with computed next Inventory, Stored after, output availability, and NodeLaw. It should not take completed graph, caller success, future ranges, future state laws, or a semantic parent answer.

The edge endpoint adds effective own-empty and Regions of the original children, resident original edge, and ActiveAbove its edgeRank. It should return actual EdgeCall, strict reads, Checks, Post, Stored after, result residency, and Shape relative to the candidate edge. Shape is needed before descendants. It is not a promise that final rebuilt descendant children equal the original children.

Use strong induction on the concrete request rank, with node and edge cases together. NodeRank is `2 * ordinaryHeight + 1`. EdgeRank is `2 * (edgeHeight + 1)`. Existing `edge_lt_node`, `child_lt_edge`, and stored Shape.height supply strict request descent. Internal row and child-list loops use finite list recursion. They do not require a future key inventory.

The other six families can be helpers of that induction:

- NodeBody: terminal cases need no recursive callback. An ordinary body traverses Rows with only strictly lower edge calls, then performs literal modifyNode. A convenient active input for an ordinary body is ActiveAbove `(nodeRank request - 1)`; the stored owner itself has the larger node rank.
- EdgeBody: ParentPlain.finite supplies the actual body, strict reads, Post, and Shape without any outer recursion. Stored advances because the outer result tables stay unchanged.
- Rows: process edge call, descendants of its returned edge, then the suffix. Return Post, Stored, resident rows, and RowsLaw at each prefix. Carry a concrete rank ceiling for all source row edges.
- Descendants: derive the actual inherited-first prefix through `InheritedPrefix.resident_finite`. It supplies the exact combined payload, readiness, and current operation state. Returned Shape supplies Regions and a strict rank ceiling for the children. Finish with literal same-arity raw rebuild; it changes no outer memo cell.
- Children: contradiction erases slots directly. A live value invokes the finite indexed Walk. No unrelated sibling closedness is needed.
- Walk: `PartialStepEffects.descent` derives the actual child payload and prefix Post. Invoke the strong node IH only for the current available Region child below the rank ceiling. Restore the original ancestor bound through the completed head before processing the tail.

Private higher-order list helpers may consume the strong induction hypothesis. The final public endpoints must discharge those helpers. A public assumed universal recursive completion callback would leave the main obligation unproved.

## Exact active and stored lifecycle

At a real start, `node_push/edge_push` derive lower recursive active bounds from the stored owner and current source key. `beginNode_except/beginEdge_except` retain the stronger ancestor bound while excluding only the selected owner. After each completed recursive prefix, `PartialActiveFrames.NoNewActive.activeExcept` restores that bound at the actual returned caller. The existing forward Frame theorem, from Protocol, separately retains the exact evaluating owner until finish. Neither direction substitutes for the other.

Cache the Shape at the edge finish immediately after EdgeBody. The source later processes descendants of that returned edge outside the edge memo. The raw descendant rebuild can contain recursive node results and need not have a three-way Shape relative to the original input. It is not the cached parent result. Node completion and ordinary modifyNode affect only the node result family; they do not require a new edge Shape.

Warm edge hits use Stored.Shape for the captured owner plus actual operand equality. Shape.regions and Stored.child then derive BOTH returned-child Region and strict recursive rank. A height-only invariant is insufficient to preserve the domain.

## Opaque terminals and limits

Empty and union bodies return directly. Mu uses `CurrentAllocatedMuRebuild.resident_rebuild`: current readiness, filtered probes, and actual Mu availability derive a same-heap completed reconstruction with result `cleanup Mu`. Cleanup can remove an unused binder (`InternedConstructorTemplates.cleanup`). The current pass does not recurse into that returned result. Do not add a returned-node Region or height law merely from Region.binder; no such law is required for one-pass completion. Region forbids a directly traversed reference, so its unexpected-reference body is excluded by the structural domain.

The principal missing proof is the joint rank/list induction constructing all eight graphs, strict reads, Checks, Post, and Stored after from these initial facts. ParentPlain, PlainInputs, active restoration, and the structural result lifecycle are component dependencies, not that induction itself. General constrained completion outside Region, repeated-pass domain preservation/convergence, literal host maps and machine IDs, GHC forcing/publication, and complete frontend correspondence remain separate.
