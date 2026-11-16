# Actual past producers and one next-query continuation

UNCOMPILED candidate. No live Source change or compilation was performed. The original arbitrary warm-history and same-root finite joint-witness targets remain open.

## Existing producer coverage

`SourceCurrentAllocatedNativeNodeReturnOrigin.returned_node_cell_finish_prefix` at260 and the edge counterpart at `SourceCurrentAllocatedNativeEdgeReturnOrigin.lean:261` already cover EVERY returned handle/request/payload. They accept an arbitrary initial Control and Output type. Their initial state has BOTH complete memo families empty. They return exact prefix, finish, suffix, counts, original evaluating owner and full states. No new equivalent wrapper is needed.

`SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace.bind` at68 and `Trace.trans` at48 splice actual completed query calls. If an old trace ends at `.code (.pure value)` in `middle`, and the next trace starts `.code (.node nextRequest .pure)` in EXACTLY `middle`, the literal composition is:

```lean
(oldTrace.bind (fun _ => .node nextRequest .pure)).trans nextTrace
```

It starts the old request with the actual next request as its continuation. It keeps all inherited memo tables and the exact intermediate Checked state. Each original count/fuel bound remains intact; the composite count is the sum. Applying the existing node/edge origin theorem then yields all-cell finish provenance for that composite execution. This is structural provenance, not a source-profile result.

The private `trace_returned_or_finish` helpers in those two origin modules already handle an arbitrary warm start: a returned final cell was present before or has an actual local finish. They are PRIVATE, not dependencies of this candidate. The generic `NodeQueryDispatchOrigin.descent` at130 similarly proves dispatch ancestry for Clean control and native Shape. Its public dispatcher at297 specializes to one initial root query. No visibility change is proposed here.

## Exact remaining semantic boundary

`GeneralCMHistoryDefinitions.AuthenticEntry` at43 names a single `.code (.node rootRequest .pure)` execution from `initial`. Its MixedQualified and NodeResult clauses retain that same execution. A second external query after the old root reaches `.pure` is not a prefix of that old root execution. A composed continuation has genuine finish receipts, but current source C/M qualification cannot silently be rebased to that different control or to tables that are already populated. A new actual entry can also add a mixed qualification that the older conditional NodeResult did not cover. Unchanged tables alone do not solve that change of qualification.

`PastEntryInnerPayloadTransport.inner_payloads_of_past_authentic_entry_at_equal_key` at25 is already a full-memo producer for all FOUR inner clauses at any actual prefix of its old cold-source history, including its endpoint. It does not transfer the proof across later native producers. Contextual/Scoped/Grows resource records also do not assert these exact source auxiliary payload shapes.

The first further warm-history case remains a cell produced by a later query that itself inherited tables. Its actual dispatch/body finish and original source entry must be related to the new mixed/auxiliary qualification, including a possible later authentic entry. The old full P, height, request/entry orientations, actual domain keys/handles and full common-reader states must remain exact. A generic past-cell or equal-key assumption cannot replace that derivation.

## New bounded call-site bridge

The public header was frozen FIRST, SHA bf1a171708e24e789ec12dcc18790c4250ba839b1b0351d7cc35d4d670540af5. It retains the accepted original source, original stored full U, full original P through an actual AuthenticEntry, the original cold-root trace/common reader, original input/field plans and same-key domain premise of the accepted transport theorem. It adds only the new request, its supplied newFuel, and the new call's ORIGINAL InputsThrough/FieldsThrough at that SAME actual reader.

The new named theorem is `SourceCurrentAllocatedNativePastEntryNextQueryInnerLaws.next_node_query_preserves_actual_past_inner_payloads`. Its conclusion concerns the literal `execute newFuel (.code (.node newRequest .pure)) reader`. It retains all FOUR whole-table laws at EVERY endpoint and both node result laws for every actual raw count at most newFuel. It uses no observation step or raised runtime fuel. Both proof paths refer to that identical execute expression and full Checked state.

The proof obtains inherited laws from the accepted transport at `prefixCount=wholeCount`, not from a Returned/innerPast premise. PrefixOperations derives current Physical, original-source growth and Ops.Valid from the actual old trace and old plans. SourceBodyFirstActualMuCutoff/ReferenceRead and SourceDiagonalFirstActualMuBody/KeyRowInputs/KeyReferenceRead derive every static compiler/read/pure/key condition from the actual common reader. The existing two warm family engines then consume those derived laws and the original new-query plans. The two private source-static derivations reuse the checked authentic-history proof paths. They do not copy the cache induction engines or create a new cache/model framework.

This is one continuation from an endpoint of the old cold-source execution. The old endpoint may be a bounded prefix; the theorem does not assert that an external source worker actually issues the new call there. The real caller must supply its action equation and original new-query plans. It does not establish an arbitrary sequence of warm producer qualifications, original full C/M admission, or one finite compatible assignment/completion. No future physical state, P availability, payload law, semantic model, child result or compatibility supplier is added.

## Check material

`PROBES.lean.txt` has appendable #check/#print axioms commands and no imports. The full public header is byte-exact inside the558-line raw module. Private helper statements are frozen separately. Existing exact producer/engine headers and source hashes are retained. All candidates here remain uncompiled until Root checks them serially. Earlier failed packets and logs remain unchanged.
