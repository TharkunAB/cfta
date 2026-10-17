# Actual node-body publication reconstruction

The final source is SourceCurrentNativePublicationNodeAlignment.lean.
Its SHA256 is 708b81d7b2517064e22c4bf8c1565c8cb1b4502a04f85a97fd5a32c63299d4ac.

`publication_node` consumes an actual Publication with a node source body.
The child premise is indexed by actual strict syntax membership and size.
It does not assume alignment of the complete source body or a stored result.
`publication_node_binder_free` derives every child case from static BinderFree syntax.
Captured values and replacements can contain recursive Mu values.

The publication supplies the actual Depth, ordinary, reservation, and body schedule.
The proof extracts both raw calls and their actual filter pairs.
Actual node construction returns an ordinary value, so both root filters are identities.
Actual Depth and missing-key freshness derive compatibility on live captures.
Unused captures can alias the ordinary marker.
`Keeps event.afterBody common` supplies the past reader's Ready, growth, and issued history.
The proof constructs both filtered stored reconstructions in sequence.
It returns their exact common final replays, Keeps, availability, local histories, and Related.

The fixture constructs a closed raw Mu replacement from empty source state.
It constructs an actual used publication with nested child unions, duplicate rows, and a dead row.
An unused captured reference equals the actual ordinary marker.
The source binder has an actual cold completion and an exact full-state warm replay.
The new static endpoint constructs both filtered reconstruction calls.
No successful reconstruction or final observation is supplied to the fixture.

Selected checks: direct-4 empty; canonical-2 pass603; public-1 full2; kernels-3 empty; kernels-public-1 full1.
Every selected run uses pinned Lean4.34.1, memory.max/high=4294967296, and swap.max=0.
Every final probe has all8 explicit printer/linter options and only standard axioms.
Failed direct1/direct3 and kernel1/kernel2 remain immutable with raw logs.

Boundary: this is a node-root publication candidate theorem.
It does not prove union-root filtering, nested binder alignment, older-winner alignment, or outer termination.
Unused smart cleanup remains the separately checked chronological history law.
