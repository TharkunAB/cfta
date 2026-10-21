# Actual native request position transport

Reviewed 2026-10-21 03:19 CEST. This is an unproved implementation plan. It owns zero Lean jobs, zero public proof pairs, and zero constructed examples. It changes no official file. Source snapshots and hashes describe the reviewed inputs.

## Recommended first theorem

Use the existing observer `SourceCurrentRequiredPositivePosition.PositiveAt`. Its paths contain natural child positions. Ordinary row choices and union choices remain explicit receipt indices. A union adds no path position. Mu and reference values have no positive-position constructor.

Implement one source-scoped actual request endpoint first. The following is a contract outline, not checked Lean syntax:

    request:
      before = <Thunks.initial width machine, operations>
      source = machine.heap
      Good before
      SemanticReady source
      ConstrainedCapGuardHeap.Heap Plain source
      NativeMuPublication.History empty source
      Available source left; Available source right
      left.free=[]; right.free=[]
      Cap Plain depth left; Cap Plain depth right
      Trace fuel (.code (requestNode emptyDomain left right)) before
                 (.code (.pure result)) after
      --------------------------------------------------------
      forall p, PositiveAt result p ->
        PositiveAt left p or PositiveAt right p

Here Plain is `fun guard => SourceMemoGate.plain guard = true`. The native memo tables are empty at this public entry. The constructor heap and equality-operation tables can contain actual prior source allocations. The trace is the actual physically admitted checked trace. It supplies instruction checks; this conditional result theorem needs no numeric capacity bound and does not construct a return.

Good supplies the coherent source facts and actual equality-field validity. `ConstrainedCapOriginalSupport.closed_inputs` derives Original, source availability, and domain coverage from these closed operands. `OriginalSupport.empty` discharges root bindings. `AllocatedRecursivePrefixState.initial`, `AllocatedRecursivePrefixCode.request_node`, and `SourceRecursiveIntersectionSourceInventory` construct the existing physical and domain certificates. Do not add Original, NodeInputs, a desired result relation, or a future enclosing return as redundant public premises.

For an actual source construction, `AllocatedNativeOriginalHistory.constructed` derives Good, SemanticReady, availability, closedness, and Original from the actual empty build plus covered guard-allocation history. `ConstrainedCapGuardExecution.closed_heap` derives the guard store. `NativeMuPublication.closed_history` derives the causal Mu history. None of these derives arbitrary operand caps or Plain support for an arbitrary nonempty root domain.

Keep the conditional internal node law for every supported depth:

    OriginalBindings Plain source req.domain.key ->
    NodeInputs source req ->
    Cap Plain d req.left -> Cap Plain d req.right ->
    forall p, PositiveAt result p ->
      PositiveAt req.left p or PositiveAt req.right p.

Pair this with the existing conditional NodeLaw, rather than discard its returned cap. OriginalBindings and NodeInputs are genuine source restrictions of the reused physical/original-domain proof. They are not output-position assumptions. The source can change sides at different child depths. No one chosen operand must support the complete result.

An internal row observer must retain either the root full-guard position or a selected child at its exact natural index. The conditional edge law gives the same-path disjunction for the two actual captured input rows. Include nullary rows; do not require a child to prove the root guard case.

## Smallest proof route

Use an additive PRIVATE history-threaded certificate/cache/trace proof. Preserve every old declaration. There is no need to add a public evaluator or replace the checked interpreter.

1. Pair the old Context with `Nonempty (NativeMuPublication.History empty current.heap)`. Derive this additional fact from the actual primitive step or completed child trace. Extend the private Return and continuation certificates with the same fact at the exact returned state.
2. Pair old NodeLaw and EdgeLaw with their conditional same-position laws. Use the generic `AllocatedNativeContextCache.Returned` predicate for actual returned cells. Empty tables satisfy it vacuously. Actual lookup and demand preserve it. A protected finish installs only the law already proved for that exact evaluating request and actual returned body value.
3. Follow `CheckedJointTrace.completed` and `CheckedJointInduction.bind/node_bind/edge_bind` by strong induction on actual fuel. Split actual compiler bodies from their protected finishes and continuations. Both completed body and continuation traces are smaller. This is induction over a supplied finite execution, not a runtime rank or termination proof.
4. Add the node-branch and checked edge-body position certificates. Derive intermediate caps from the existing paired node/edge laws at the SAME returns. Consume the checked `NativeMaybeMuPositivePositions.maybeMu` once at the actual optional constructor cut.

Why the old Certified cannot be used unchanged: `ConstrainedCapKernelJoint.Context` (lines 27-38) has semantic heap, guard heap, physical validity, source growth, and issued-map extension. It has no causal MuPublication history. `CheckedJointCode.Certified` (lines 42-65) quantifies over child and primitive returns with only that Context. Such an arbitrary quantified return cannot supply the causal history required by maybeMu. Adding a stronger final postcondition alone does not repair this intermediate-state gap.

Use `NativePublicationTrace.step` or `from_history` at the exact actual trace cut. Do not derive causal history from Grows, Keeps, issued extension, native memo History, or the scalar guard profile. `ConstrainedCapNativeGuardHeap.step_heap/trace_heap` preserves the guard store through actual admitted effects; `ConstrainedCapGuardNative.stored` derives the MuStored premise at the current cut.

A pointwise trace-cut proof is an alternative. It still needs a conditional returned-cache law for warm lookup, the protected-finish induction, and inversion of each compiler/ordered-walk branch. It would duplicate those inversions without removing the causal-history obligation. The private additive certificate route follows the checked existing proof more directly. Do not strengthen the old public Certified type.

Expected size is about 600-900 new lines if physical/cap facts can be reused at actual cuts. This is an estimate. Stop and simplify if the proof starts to copy the complete physical or semantic completion framework. First check the optional-constructor continuation, protected finish, and indexed walk subproofs; these determine whether the estimate is realistic.

## Exact branch obligations and existing inputs

- Empty: the literal result has no PositiveAt. Self: `SourceRecursiveIntersectionControl.self_record` identifies the actual complete result with the queried operand. Top has no separate compiler branch; use the literal empty/reset/self/swap/repeated/payload decision order. Plain Top-like rows cannot introduce a positive root guard, but may have a positive descendant that still needs the ordinary child proof.
- Reset and swap: retain the actual normalized child request and convert the disjunction back to the original left/right order. Repeated: the literal intersection reference is opaque and has no PositiveAt. Unsupported branches cannot appear in a completed successful trace.
- Ordinary root: invert the actual makeNode normalization to an actual returned row. In the accepted checked edge-body branch, use the exact loads, allocation run, combined guard, and readback. Actual conjoin_plain gives: if both source full guards are Plain, the output full guard is Plain. Its contrapositive gives the desired source-guard disjunction. A rejected or mismatched branch returns the actual Top/[Empty] sentinel, which has no positive position. Cover nullary rows without a child-existence assumption.
- Ordinary descendant: retain the SAME row child index through the exact zip and ordered walk. Apply the conditional node law to that actual child pair. The current private `CheckedJointEdge.certified_walk` preserves result membership; that fact alone does not identify an output child index with the source index. Add an indexed All2 walk proof or reuse an exact actual walk decomposition. Duplicate equal child values must not change physical positions.
- Union: invert actual makeUnion canonicalization to an actual member with PositiveAt at the SAME path. The already checked constructor inversion in MaybeMuPositivePositions is private, so copy only the required local proof or factor it in the new owned file. Keep the actual ordered request member and continuation; do not turn a canonical row position into a child-path position.
- Mu: actual `compileMu` performs identities, enter, one body request, and maybeMu. `ConstrainedCapNativeScope.body_cap` retains each body cap. For a Mu operand, `mu_annotated` makes its exposed body hereditary Plain; positive body paths on that side are impossible. For a non-Mu operand, body is the literal input value. The body request yields its actual finite cap. The new maybeMu theorem maps its returned PositiveAt to the SAME path in that body-request result. The body child law then chooses the original side. Do not identify the cached winner body with the current incoming body.
- Reference: a bare reference is opaque even if its stored binding is constrained. Therefore legitimate Plain binding support is necessary. `OriginalSupport.enter/extend` derives it for actual bindings introduced from capped Mu operands. `OriginalSupport.read` returns the SAME complete available annotated source Mu after real growth and issued extension. PositiveAt on that read Mu is excluded by `RequiredPositivePosition.not_plain`; the other operand retains the same path. Missing reads or missing names exclude successful completion.

The checked optional-constructor primitive is now available at `SourceCurrentNativeMaybeMuPositivePositions.maybeMu` (lines 493-539): SemanticHeap, Available incoming body, finite Cap Plain, current MuStored Plain, causal History empty current heap, and the actual maybeMu.done equation imply same-path transport. It does not need PlainDomain, Ready, ProbeFree, or an assumed output-position law. Its proof already handles the current ordinary callback and retained warm winner separately, including intermediate MuStored preservation by actual callback execution.

`SourceCurrentNativeStoredMuPositivePositions.reached/source` is useful readback prior art, but its conclusion alone only relates finish to the SAME stored ordinary probe. It cannot replace the checked incoming-body maybeMu theorem.

`SourceCurrentMergePositivePosition.run/call/worker/allocated` and `TargetOperandPositivePosition.project/operand` are downstream class/target tools. The native compiler does not call the class Merge worker. Reuse constructor inversion facts where applicable, but do not substitute Merge's input-source law for a native request proof.

## Warm native winners without a caller-supplied law

The private paired returned-cell law must cover all captured requests conditionally. Internal warm hits then reuse laws installed by actual earlier protected finishes, including earlier sibling calls. `CheckedJointCache.node_observed_ready/edge_observed_ready` and `CheckedJointTransition.node_yielded/edge_yielded` show how physical validity, KeySafe/word checks, actual lookup, and actual demand align captured with queried. Shape or key equality alone is not full request equality.

Do not implement the public theorem for arbitrary initially populated tables from Good alone. Good and strong writer maps establish physical provenance, not this position relation. A historical warm writer can have a longer compiler body than the present one-step lookup; induction on the present query's fuel cannot recurse into that unrelated historical body.

If a warm public endpoint is needed immediately, add at most one `requests` head for an actual ordered `Code.walk` of empty-domain queries from the same empty native tables. Its inputs must be source-resident closed pairs. Its returned list must retain the exact input/output index. At each pair's finite cap depth, the result has same-path OR-input support. This derives cache laws internally and tests actual warm reuse. It takes no positional cache premise and no arbitrary caller-written finish instruction.

For later generated closed operands, retain actual prior returned-cell origins and use the existing rebase route. `CheckedJointRebase.node_law/edge_law` (lines 68-94) derive old bindings through `CheckedJointOrigins.bindings_back` and old input support through the SAME captured origin's inputs_back. A positional rebase can reuse those facts and apply the old conditional position law; its conclusion does not depend on sourceWeight. The actual prior origin/cache receipt is essential. Bare Grows cannot create it.

This rebase is a proposed follow-up, not a proved consequence of the present plan. A fixed-source request or requests theorem does not yet cover a new input generated after that source heap. Preserve that scope until the actual origin and positional cache receipts are composed at the warm query entry. Do not treat the current warm_complete signature, which accepts old joint cell laws, as an already derived positional warm law.

## Scope, falsified shortcuts, and checks

The checked `PositiveNativeSupportKernels.actual_opaque_mu_counterexample` has source-built closed raw Mu inputs, empty native result tables, initial Good, and a real completed native request whose ordinary result is positive at []. The inputs have no PositiveAt because Mu is opaque. Thus source initialization, Good, and closedness do not prove the unrestricted OR-input law. Finite Cap Plain excludes that example by hereditary Mu Plain. No new counterexample or Haskell defect is asserted here.

Initial source construction does not prove PlainDomain for an arbitrary caller-selected domain, finite caps for arbitrary operands, or a position law for arbitrary warm cache contents. Preserve explicit source and guard-allocation premises. For the empty root, domain support is vacuous; it is derived from actual enter/read at recursive cuts.

A minimal nonvacuous check should use actual source-built ordinary rows with Plain parents and a nonplain child at index 1. Put a positive source on different sides at two child depths. Include repeated equal child values and an actual second equal request that hits a returned native cell. Preserve index 1 through the checked zip/walk. Separately exercise a genuine compileMu/optional return with capped Plain Mu operands and a positive non-Mu side; all-Mu Plain inputs have no positive output and cannot alone validate a positive witness. These are proposed examples, not new checked fixtures.

This plan proves no first-ordinary cut, original slot identity, global renewal rank, native termination, whole outer completion, failed-state support, or production Haskell correspondence. Class chronology and Rel transport remain separate. The existing counterexample also leaves the no-finite-cap opaque-barrier case open.
