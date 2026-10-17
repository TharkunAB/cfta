# Independent operation growth review

The reviewed final sources are:

- `SourceCurrentOperationGrowth.lean`: `06fefb19c82c5a17626576a65646f75f8079b4413792281e2218d6e1a690e66b`.
- `SourceCurrentWorkerOperationGrowth.lean`: `19aba250abb544fd0de2f4374f42455d8f649a95fab512df5d77f40edda32374`.
- `SourceCurrentOuterExecutionGrowth.lean`: `4c62b507158c680798dafbfa10d3f7b5bfe60d8309a37a928f4fc6db16d725ac`.

The review found no material issue.
It used source inspection only and did not run more Lean builds.

`Grows` contains actual constraint-cache `Steps` and extension of both completed operation tables.
It preserves earlier entries, including on malformed inputs and stopping outcomes.
It does not prove that new completed operation entries are valid.
The primitive proof covers accessor, combine, descend, precheck, constructor, inherited prefix, tuple fold, and every checked native outcome.
Native yielded execution composes the actual first step with its continuation.
Native done, failed, constraint error, and blocked outcomes retain that same actual first-step state.

The lower-worker proof follows the actual bind schedules.
It retains the right-fold class order, interleaved target work, required preparation, native calls, parent rejection, field faults, and constructor faults.
Projection and head operations retain the operation component exactly.
No completed graph, range certificate, Cap, or closure premise replaces a worker branch.

The outer proof follows the literal fuel decreases in rows, descendants, and indexed walk.
Ready, busy, and absent demand branches retain their actual post-demand operation state.
Evaluate branches use the captured original owner and the actual body result.
The `Step` and `Reached` proofs use exact completed earlier row and child returns.
They do not infer a future return from a reached phase.

`ready` transports one initial ready constraint value through derived constraint-cache extension.
`field` transports an actual successful original field load.
`cache_valid` requires initial constraint-cache validity and proves only that cache validity.
`identity` also requires ready operands and equal identities at the reached reader.
None of these theorems infers full equality-operation memo validity from extension alone.

`GrowingAncestor` retains the exact activation, owner request, handle, and operation growth to the reader.
Its activation cell is evaluated at the captured running state.
Current evaluating membership is a separate premise or conclusion in the initial busy theorem.
The initial theorem derives reached ancestry from an actual busy failure with initially empty outer result tables.
It does not derive a busy failure, exclude busy keys, bound fresh requests, or prove termination.
The remaining progress obligation must exclude physical key collision with every live ancestor using actual parent and inherited-request lineage.
