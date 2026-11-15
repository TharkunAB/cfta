# Existing writer APIs and the remaining link

`SourceCurrentNativeNodeWriterHistory.writers` at
`lean/MicroCFTA/SourceCurrentNativeNodeWriterHistory.lean:273`
uses `SourceCurrentNativeEdgeWriterGrowth.History`.
Its `Written` result at line30 retains an actual compiled body trace, evaluating
owner, protected finish and both writer-heap growth facts. The `warm` theorem
at line283 identifies a ready hit's exact request and returns that same receipt.

This is useful existing provenance. It does NOT include a prefix from the
particular original control/state supplied to the current proof. The `History`
index retains only the current state. Thus the existential `Written` trace must
not be attached to a separately supplied execution by matching its cell key.

This new candidate extracts the actual indexed finish from the given trace.
The remaining exact call-site obligation is to derive an earlier prefix in
that SAME trace to the node query dispatch and captured
`(compileNode request).bind (fun result => finishNode handle result (next result))`,
with the SAME complete original request/handle and genuine raw body segment.
The captured continuation can include outer parents. Keep full checked states,
original supplied count/budget and both operand orders where source M uses them.
Do not replace this obligation by arbitrary same-key or same-ID witnesses.

Actual_edge_footprint owns that earlier compiler-dispatch link. This packet
contains no duplicate proof and makes no claim that this remaining link holds
for arbitrary initial Code.
