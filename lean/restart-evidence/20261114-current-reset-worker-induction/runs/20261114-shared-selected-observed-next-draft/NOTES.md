# Actual completed selected receipts: replay and full prepared-row resources

Status: UNCOMPILED. Root owns all compilation and publication.
This packet contains two proposed source modules and static checks.
No compiler was run for this packet.

## Existing and missing producers

SelectedEdge.complete_with_fragments_resources already supplies the actual
selected-edge result and full child resources at derived adequate bounds.
CapturedEdge.complete_with_history_resources_prepared already supplies the
actual captured result and its original full resource packet at those bounds.
Its prepared parent is available and closed. It need not equal the parent at
the original stored handle. SharedNativeBranchCompletion.head_complete_resources
projects a weaker packet for the stored-parent case.

These existing producers do not attach their full packet to an arbitrary
actual completed observation at smaller bounds. Existing observed scalar and
properness laws also do not supply that full packet. Root checked the opaque
completed-observation producer separately. This packet addresses the ordinary
selected-child tuple and captured finalization.

## Proposed successful replay

SourcePruningEnumerationSharedSelectedEdgeStability.lean adds four laws.
ChildTraversal.Trace.moreBounds replays each exact actual singleton child call
through checked ChildDispatch.run_singleton_stable. The traversal law derives
the trace from its actual completed observation and replays that trace.
SelectedEdge.complete_stable preserves the actual cached own-class prefix,
child tuple, fragment and residual update. CapturedEdge.complete_stable then
preserves the actual successful finalizer through the existing pure finalizer
more-fuel law. A finalizer stop cannot satisfy the completed observation.
Each primitive bound can increase independently. No resource premise is needed
for these replay laws. Every called child and selected operation is the actual
shared implementation. No legacy worker or child is substituted.

## Proposed observed resource producer

SourcePruningEnumerationSharedCapturedPreparedObservedResources.lean retains
every initial premise of complete_with_history_resources_prepared byte for
byte, except its new theorem name. It adds only the five current bounds and
the actual current completed receipt. It compares that receipt's replay with
the original producer at the sum of both sets of bounds. Receipt equality
identifies the exact caller, saved queries and complete cache. The proof
returns the original retained resource conjunction.

The conclusion retains every original field: execution, Post, exact query,
counter growth, roots, storage, realized pending values, waiting index,
expandable index, non-target enumerated origins, pending inputs, protected
roots, pending references, complete or stopped shape, order progress, Fits and
Heap. The received completed observation eliminates the stopped alternative
inside the proof. The statement retains the original alternative structure.
Explicit actual constructors give standalone equalities an expected receipt
type. The resource conjunction roundtrip is byte exact after replacing only
the observed receipt and its endpoint variable names.

The derived adequate bounds remain existential conclusions. They are used to
compare two executions. No future observation, sufficient-budget result or
callback resource is added as an input premise.

## Validation and limits

ORIGINAL-PREPARED-PRODUCER-HEADER.lean.txt preserves the exact current public
producer header. NEW-OBSERVED-PREPARED-HEADER-UNCOMPILED.lean.txt records the
proposed header. RESOURCE-CONJUNCTION-ROUNDTRIP.json records the exact resource
text comparison. Source pins record the current actual operations and laws.
The virtual import graph is acyclic. These checks do not give proof credit.

Root must check the replay module first. Root must publish it as a normal
dependency before checking the observed-resource consumer. A partial private
object tree must not be used as a namespace overlay.

These laws concern the actual SelectedEdge.run and CapturedEdge.run workers.
They do not identify that shallow child policy with eagerChild. The eager
prepared scan still needs its genuine child-measure induction, all emitted
resources, callback endpoints and captured-cache framing. The complete worker,
the common finite original-root witness and generated-Type closure stay OPEN.
No Haskell defect is established. No Haskell code, contracts or FINDINGS file
changed. The clear-writing checks were applied to this note.
