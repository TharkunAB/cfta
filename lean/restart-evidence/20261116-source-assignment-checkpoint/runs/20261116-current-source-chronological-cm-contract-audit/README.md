# Chronological actual source C/M contract

Status: read-only design audit. The header in NEXT-SOURCE-EVENT-HEADER.lean.txt is UNPROVED specification only. There is no new theorem, engine, history record, or semantic supplier.

## Minimal adaptation

GeneralCMHistoryDefinitions.AuthenticEntry:43 stores genuine ordered enter data, but fixes its trace start to <initial width machine,operations>. SourceCanonicalOldEntry.stored_dispatch_canonical_old_entry now derives the same event data at arbitrary inherited Caller.checked. That state is not definitionally the cold initializer.

The smallest logical adaptation is to parameterize that existing event relation by the actual Checked start. The cold definition must remain an exact specialization, with old APIs unchanged. Its full original P, closedness, identity, node-or-union tag, both orders, actual count, domain allocation and actual entry step remain identical. The dependent M/node/edge qualifiers must use the same actual start. No Profile(P) condition is justified or needed.

This scope change does not establish the inherited memo law. That law must come from chronological induction over the real source execution. The source-event header records the first missing producer needed by that induction; it is not an inherited-law premise.

## One precise source-history contract

Fix the accepted original source, its full stored U/body metadata and one complete finite observed source execution H at the original budgets. Include every actual native execute occurrence at SharedIncomingNode.run:68, SharedDispatch.dispatch:83 and SharedTargetWorker.step:58. Include nested enabled-emptiness calls. Keep their exact before/after Checked states and real intervening source operations.

At every observed prefix of every such call, both complete native memo tables must satisfy the C/M conditional laws relative to every genuine original canonical U/P entry ANYWHERE in H. In particular an entry may be later than the prefix or ready-cell birth being checked. Original full P and its original height remain unchanged. The ordered edge law uses every actual original zipped child occurrence. The same history contract includes both BodyFirst and Coherent node/edge laws for every genuine base entry in H.

There is no Gamma, Profile(P), payload result or ownership assumption in this target. It is a statement about actual calls and events of the fixed run, not a new record with desired semantics as fields. A stopped call is a retained endpoint. Earlier successful prefixes and outputs remain covered after a later stop. Both complete initial memo families are the real empty initializer.

The induction order is outer actual native-call count, then actual prefix/finish count within the current call. Fix H before induction. Restricting admissible entries to calls earlier than the current prefix would weaken the original later-entry target. At an older producer, the IH can therefore be used for a later genuine entry in H, after the actual ownership/canonical-entry data is derived.

## Exact first missing source event

The checked ancestry theorem starts from a supplied literal enter prefix. The checked source operand and canonical-old-entry receipts also start from that enter. None constructs its existence from an issued node request's domain.

NEXT-SOURCE-EVENT-HEADER.lean.txt asks for precisely that missing construction. It starts from actual stored/decoded root slots, current physicality, a literal empty-root Trace to an issued node and that node's original singleton domain key. It derives a prior actual enter in the SAME producing call, its exact full domain handle, actual step and suffix, closed full operands, and their captured IDs. It accepts no ownership, AuthenticEntry, Gamma or old-parent-empty premise.

The header uses structural UID/patternId keys only. It adds no restriction to full P. The public canonical-old-entry producer then consumes the genuine later full-P entry and common-reader traces to identify the complete U/P operands and their original height. The source-event component is not a replacement for that full-P goal.

A proof must track actual domain origins through generated controls: same parent domain, reset to empty, or the domain returned by an actual enter. A cached domain allocation still has a real enter event. Warm native request-exactness identifies cached evaluate operands with the actual issued request. The existing empty-root singleton-enter theorem then derives that the creating parent is empty. Source closure and represented-empty-handle facts finish the stated receipt. No generic graph invariant or semantic cache framework is required.

## Existing source call order

SharedCachedTerminal.rawFold:47 recurses on actual sources only after a literal singleton successful captured action at lines 65–71. It retains reachedCaller and savedQueries. It is not a list of independently initialized intersections.

SharedDispatch.afterQuery:35 may run SharedEnabledEmpty.check before rawFold continues. The enabled Worker can perform additional native calls through the target worker. Induction on rawFold.sources alone therefore does not order every native call. Use actual chronological native-call count across these nested source operations, with the existing structural worker/task induction to derive the ordering.

Constructor-only operations use actual advancePhysical and its advance_tables:111. Post.effects.keeps supplies both heap growth and issued-history retention. Native query operations use their real Trace extensions. These actual frames compose a common reader; a heap obtained after an external source action is not automatically a native Trace suffix.

## Dependencies and exact remaining work

1. Prove the source-event header. Extend the already checked syntactic source-domain argument only with actual prior-event witnesses. The witness is a result, never an input oracle.
2. Reuse SourceCanonicalOldEntry.stored_dispatch_canonical_old_entry, now public, to recover the full actual ordered event and full P availability at old birth. SourceEnterFullOperands and SourceEmptyEnterOperands already discharge its old closedness and ID qualification. No Profile(P) is required.
3. Expose/use the existing private NodeReturnOrigin.trace_returned_or_finish and EdgeReturnOrigin.trace_returned_or_finish as actual retained-or-local-finish observers. They already accept arbitrary warm starts. Repeat the retained branch through earlier actual calls; the actual initial complete tables eliminate it at the base. Do not duplicate these proofs.
4. Use the existing private NodeQueryDispatchOrigin.descent and edge counterpart to obtain actual dispatch/body origins from Clean source control and physical Shape at an arbitrary warm start. Their general cores already support that scope; public from_initial_query_finish wrappers currently pin cold starts. Add only source warm wrappers if needed.
5. Instantiate SourceQueryInduction.query_returned_and_raw_results at the current real start, with the SAME fixed-H conditional laws. Its prior Returned inputs are supplied internally by the earlier-call IH after the event ownership and full-pattern transport above. Do not publish them as new source assumptions or add another generic engine. Existing full C/M raw/body finish cases need their root-prefix scope adapted to the actual start; semantic cases and original height/fuel bounds do not change.
6. For old edge cells, reconstruct every original child C/M qualifier under the recovered old event. The node-only payload theorem is insufficient. For auxiliary cells, retain the full actual base/diagonal/body enter chain and derive the four family priors from the same earlier-call IH. The already checked next-query inner-law theorem is exactly a recurrence for a fixed base key; it does not create old entry ownership or prove the C/M law.
7. Derive original per-call physical/input/field checks from actual source entry invariants and source resource receipts for all three call families. Preserve each call's original supplied budget. WordRanges and resource growth alone must not be renamed InputsThrough/FieldsThrough without the actual admission producer. No forall-future-call plan is added as a supplier.

The source operand route currently proved here covers two stored dispatch operands. SharedIncoming's incoming prepared child and SharedTargetWorker's forced operands require their own actual source-closedness routes. Existing real task ChildInputs and closed reader/exposure facts are candidates; this audit does not grant those unproved producers.

The full warm-history theorem remains open. Profile is a closure/atom statement, not a finite inhabitant. The original same-root finite accepted completion with one assignment for every retained and historical obligation remains the main semantic objective.
