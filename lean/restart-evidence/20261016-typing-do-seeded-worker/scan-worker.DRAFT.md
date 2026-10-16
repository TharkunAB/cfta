# Literal current Scan worker draft

This draft accompanies the seeded-worker checkpoint. It is not a completed
Scan correspondence result. The worker source will be additive.

Use the new literal GateWorker primary and secondary wrappers, the new
SeededWorker, and the checked ConjunctionWorker. The GateWorker has no memo
argument. Scan threads the actual fourth memo separately. Keep primary and
secondary gate bounds distinct, then projection, read, and native bounds.
The algorithmic conjunction budget stays fixed when stage bounds grow.

For each original class, primary false selects the class and recurses.
Primary true runs secondary. Secondary true skips it and recurses. Secondary
false projects its first-seeded query, then calls the current fourth memo.
True stops before the suffix. False recurses at the exact returned checked
state and fourth memo. Empty input returns no stopped class and no selected
classes without work. Preserve selected order and repeated classes.

Every failure retains the actual checked state, current fourth memo, and
complete underlying gate, projection, native, or conjunction diagnostic.
If a selected class precedes a failed suffix, retain that selected prefix
in the failure context. Do not convert failure into an emptiness answer.

Completion must derive stable stage bounds from finite current Scan graphs.
Stability must retain the exact stopped class, selected list, complete
checked state, and fourth memo. Soundness must reconstruct the same graph
under legitimate initial facts and actual reached range obligations.
Construct strict SourceCurrentAllocatedScanSourceReads for the same graph.
Use SourceCurrentAllocatedPrimaryReads for exact primary source operands.
Global reads are logical evidence, not concrete host table events.

Then derive full caller Context/Post and actual probe heaps at the computed
next inventory. The existing relational completion and language endpoints
remain useful dependencies. No completed future query, arbitrary gate
answer, native result law, or final state invariant can be a public premise
of finite caller execution. Preserve the full library objective.
