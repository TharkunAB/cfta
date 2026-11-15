# Current Inputs at an actual native Post endpoint

Status: UNCOMPILED. Root must check the new lemma and all 64 private probes. The input is exact checked owner63 `d3ed89bf0b86fd5eaa8ed3afd6fa2e48f002309f6142a34124d66df70f042dc7`. All input bytes remain an exact prefix. This packet adds one lemma and no definition.

The lemma takes genuine point.Inputs, the actual native Post from point.caller to reached, and the returned query equality. It derives Inputs for the point with only caller and queries changed. The captured point.before, completed prefix, frame, seed, mass, height, count, bound, input list and capacity stay unchanged.

The existing tuple_inputs_captured_native_post lemma transports full TupleInputs through that Post. SourcePruningEnumerationRecursive.captured_post transports the captured Packet. Original-root heap preservation follows by composing the old Keeps with post.effects.keeps. The lemma does not take new root preservation as a premise.

All static input facts remain valid because their root heap, captured cache and bounds stay fixed. This includes original-root availability, closedness, child height, bucket length, variable bounds, pending facts, full-list membership and suspended mass. The only equality context is DecidableEq EdgeKey.

The Post is a proof-cut for an already completed actual lower task. The main rows proof must produce it from the completed lower-task resource IH. This lemma does not assume a future row result or future resource invariant. It transports Inputs only; native Fits, forecast admission and row-prefix execution still need their actual producers.

The original four worker and prepared targets and the observed prepared sixteen-conjunct target stay unchanged. The full rows and worker induction remains open. No Haskell change was identified. No compiler, live source, Git, board or /tmp write is used.
