# Independent review: actual checked contextual query readback

Date: 2026-10-16 05:00 CEST. Read-only review. No root-owned source edits or builds.
Reviewed: lean/MicroCFTA/SourceCurrentAllocatedNativeContextQuery.lean, lines1-96.
SHA256: b3d7da7d77c49a98e3ea90450f36293066734a1e873fc55abec35bfdcc5b40eb.

## Main scope finding

The conditional proofs are valid. They do not independently establish root result semantics from only smaller-child laws. In the started branch, the outer request executes its own final finishNode handle result. FinishThrough requires the local FinishLaw at that instruction. The same original evaluating cell is retained, so that check requires NodeLaw for the ROOT request and its actual result. query_law then preserves and reads that law from the returned cell.

This is an explicit remaining semantic obligation, not a Lean inconsistency. It removes the separate final Provenance.Valid/NodeProduced and rich physical InputsThrough assumptions, but it does not remove the main root-law construction obligation. The module header correctly says recursive finish-law construction remains open. Summaries must retain that qualification rather than call query_law/query_exact an independent general native soundness proof.

The next non-circular semantic step is to derive the actual body NodeLaw from branch laws and appropriately smaller-child context laws, then use it to discharge the ROOT finish check. Supplying a FinishThrough plan that simply assumes this same root NodeLaw would not complete that step.

## Exact call branches

- call_law:36-39 excludes the unresolved direct branch using KeySafe-derived represented request keys. It does not assume the missing branch semantically correct.
- call_law:40-42 uses the literal initial published returned cell. node_ready_contextual identifies the full captured original request from checked word keys, current original availability, and common physical validity. Initial Contextual supplies the historical law. The ready branch has no new body, constructor effects, or substituted result state.
- call_law:43-57 identifies the actual started request with the candidate via node_started. That theorem derives lookup validity from INITIAL physical validity and current Ready/KeySafe inputs, not future validity. Structural Shape is then advanced through actual lookup and demand.
- Actual checked body Steps begin at the real running native state paired with before.operations. SourceEqualityNativeDemandRunning.trace_retains covers actual checked edgeBody controls and retains the same evaluating handle. The proof does not replay the eager edge worker.
- The final returned cell is at the exact finishNode handle result middle.native, with the actual middle operation state retained by NodeReadback.Call.started. final.nodes reads precisely that original request/result cell. No state reset, new handle, reversed operand request, or future physical validity is used.

## Finite execution and exact model language

query_law:60-73 derives final Contextual with ContextExecution.done_contextual using the actual checked execute equation and actual FinishThrough plan. call_law receives this derived final contextual invariant. It does not take final native validity or final result availability from the caller.

query_exact:76-94 adds actual NodeInputs scope, independent rank erasure, and equality of the request domain with the empty source domain. It applies node_closed_exact correctly: empty contexts are vacuous, and the two finite original input ranks supply their inclusive sum bound.

The conclusion is the intersection of FIXED MODEL input languages. It is not directly the independent physical meanings of request.left/right without source-model/readback instantiation. Also, the statement has no left.free=[] or right.free=[] premises. Therefore the comment 'closed query' is less precise than 'empty-domain query'. The theorem statement itself is sound. Source physical meaning correspondence remains supplied by the separately derived source model interface when applying this endpoint.

NodeInputs excludes unsupported generated operands and requires the fixed model's valid original domain when the semantic law is used. This scope is explicit in query_exact. Warm initial physical validity and Contextual are genuine cache invariants; this module does not derive them from arbitrary runtime table contents or prove GHC publication/forcing.

## Result

No logical or state/provenance defect found. Preserve the ROOT finish-law obligation and model-language versus physical-language distinction in publication notes. General query completion, recursive body-law construction, and source runtime correspondence remain open.

## Parent response and final scope correction

Root accepted the main finding. The public endpoints are now named query_law_of_finish_laws and query_exact_of_finish_laws. The module header explicitly says the started FinishThrough plan contains the request's own root result law. The exactness comment now says empty-domain/fixed-model exactness. Publication notes retain the independent physical original-input readback obligation.

These wording/API corrections accurately describe the proved component. They do not discharge the root finish-law obligation. The original source hash above identifies the version reviewed in detail; root owns the rename build and aggregate recheck. No additional source work was requested or performed by this reviewer.
