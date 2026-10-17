# Independent review of shared edit row lineage

Reviewed 2026-10-17 23:31 CEST. This is a read-only source and evidence
review. It adds no production theorem and runs no build.

Reviewed SourceCurrentSharedEditRowLineage.lean at SHA
4b02b1748d11f0e5eb19cdd1f4da1f7dd44cfb7164a77c509b560b01d347d28c.
The source equals the immutable strict13 snapshot. The strict13 log is empty.
Canonical1 passes 1288 jobs. It replays the existing unused-variable warning
from InternedFreshOrdinaryClosedCompletion; the new module has no warning in
its strict log. Public1 contains three full explicit signature/proof/axiom
pairs, all eight options, and #check @. No omission, sorryAx, or pretty-print
failure was found in that selected public log.

No material proof or contract defect was found.

## Indexed prefixes

children_indexed preserves the original child index and the exact offset
lookup. The unselected case returns the original complete value. The selected
case retains an actual EditNode at the captured intermediate states. Offset
arithmetic in the recursive child case accounts for the consumed head.
The theorem does not export a connecting earlier-children prefix or its
ChildrenReads. It is an actual indexed child-call witness. It alone cannot
transport a row-start history to the existential selected child's start.

rows_indexed has the stronger prefix needed at a captured row start. Its
source edge is edges[index]. The returned raw edge is results[index]. The
existential earlierRows is EditRows over edges.take index and results.take
index, with the exact initial and captured SharedState endpoints. Its
RowsReads starts at the original memos and returns exactly rowMemos.

The successor proof constructs this prefix with EditRows.cons children
rebuilt earlierRows. The rebuilt edge equation is part of that graph. Thus
the prefix includes every earlier child computation and its raw makeEdge
advance. The corresponding RowsReads.cons threads the same memo bundles.
It does not replace the captured start with another state that only has the
same physical heap. The same captured state supplies its Ready evidence and
growth into the raw row scan's final heap.

The full source symbol, complete raw guard, and ordered returned children
follow from the actual makeEdge readback at the child return heap. The proof
uses physical field availability, input edge residency, and the derived
child effects. It does not infer a complete row from its numeric key alone.

## Canonical survivors

node_survivor first derives the completed raw scan's Ready and resident rebuilt
rows through rows_effects. EqualityLeafProjectionPhysical.makeNode_edges
identifies actual makeNode readback with canonicalEdges(surviving rebuilt).
Its coherent, linked, and resident premises come from those actual effects.
No canonical ordering premise on the original row list is added.

normalized_member then gives an exact raw rebuilt row occurrence and
physical dead=false. List.mem_iff_getElem? chooses one raw index. Applying
rows_indexed to that occurrence recovers its original source row and exact
prefix. The final constructor's physical growth extends all three captured
heap-growth facts into the actual final heap.

This is an existence result for each canonical surviving row. It permits
reordering and duplicate removal. It does not assert a bijection, preserve
normalized row positions, or preserve occurrence multiplicities. Shared
physical edge identities are handled by the imported coherent resident
readback laws. The result retains full fields rather than inferring them
from semantic equality.

## Native history at the captured row start

The current ParentNativeHistory draft has a private mutual Maintained proof
for node, child, and row reads, exposed only through edit_children. Its row
case advances native History across the actual raw constructor using
run_correct and the exact rebuilt equation. Its leaf case transports actual
Force/Target/native-query histories. Its recursive head case uses the actual
global effect's heap growth. None of these cases requires a future writer law.

A public edit_rows adapter with the same mutual motive is sufficient. Given
an initial History before.checked and constructor Valid of the initial heap,
apply it to the earlierRows prefix's returned RowsReads. Its result is History
at the exact start.checked captured by rows_indexed or node_survivor. No
additional closure, output rank, per-row writer, or future query premise is
needed for this row-start history transport.

There are two different Valid predicates. The startValid returned by row
lineage is EndpointMemoGateTrace.Valid for rowMemos. It is not constructor
Valid. The initial constructor Valid needed by edit_rows follows from the
original Ready.checked semantic facts and coherent.valid. Captured startReady
also supplies constructor validity for later operations. Do not pass the
global-memo Valid field as the constructor hypothesis.

The reviewed ParentNativeHistory draft had SHA
419fbafbbad5318f1a37e8cc7fde67c84874ae6b771f58c4800acc5a8850b5b7.
That is a review snapshot, not a claim that the pending public edit_rows
adapter has already been checked. This review does not freeze that draft.

These are completed-graph provenance and transport laws. They do not construct
edit completion or full outer completion. Physical Grows does not by itself
supply issued-reference extension or SemanticReady transport. The retained
actual read receipts supply the required semantic and physical facts at the
specific stages where the proofs use them.
