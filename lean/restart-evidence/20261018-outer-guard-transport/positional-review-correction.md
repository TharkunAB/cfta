# Correction to the fixed-own reachability review

The frozen `20261018-global-progress-review/fixed-own-reachability-review.md` interpreted the `GuardHeap Plain` premise of `SourceCurrentRequiredGuardOrigins.accepted_head` too strongly. This correction does not change that frozen file.

The premise is `SourceCurrentConstrainedCapGuardHeap.Heap Plain`. It records causal Mu body/probe profile equality. It is not `SourceEqualityAnnotationHeap.Heap Plain`, which constrains every resident raw edge guard. A mixed heap with positive ordinary row guards can satisfy the causal predicate. Actual closed source construction supplies the causal predicate for each annotation predicate. Actual preservation through later calls must still be proved.

At an actual gate-accepted Head, `accepted_head` derives `Annotated Plain result` and an empty effective own field for every exposed root row. A produced causal heap at that Head entry can discharge its premise. A global raw-edge plain heap is not needed.

This removes the stated mixed-heap obstruction. It does not prove that the fixed-own footprint cannot recur in an actual outer call. Positional ordinary-row provenance and transport through the actual enclosing calls remain separate obligations.

Source pointers: `lean/MicroCFTA/SourceCurrentRequiredGuardOrigins.lean:101`, `:139`; `lean/MicroCFTA/SourceCurrentConstrainedCapGuardHeap.lean`; `lean/MicroCFTA/SourceCurrentNativeGuardHeapReturns.lean`.
