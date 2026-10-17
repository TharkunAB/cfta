# Independent review of captured row writer histories

Read-only review on 2026-10-17 23:34 CEST. No build or source edit was made.
The prior shared-edit-row-external-review.md remains unchanged at SHA
a5b85feb132de99b309684a950a1cc8d9ba882aeaac9066947e6c20d7d22bea8.

Reviewed source snapshots:

- SourceCurrentParentRowWriterLineage.lean:
  199c9a33454b30aa1fdfa343b77e460422098d1ed6b4688292c17deed2aa7ae2.
- SourceCurrentParentNativeHistory.lean:
  7170690c80016c87593c1b0626ef722e61c36ac70ec8a51185cb1597bc989381.
- SourceCurrentSharedEditRowLineage.lean:
  4b02b1748d11f0e5eb19cdd1f4da1f7dd44cfb7164a77c509b560b01d347d28c.

The first two hashes describe the draft bytes reviewed. This report does not
claim that those drafts have completed strict or canonical checking.

No material proof-flow or contract defect was found.

## Exact captured states

The lower node_survivor returns one raw rebuilt row occurrence and its exact
source row occurrence. It also returns earlierRows over the original and
rebuilt take(index) lists, with endpoints before and start. Its prefixReads
threads the original global memo bundle to rowMemos at that same start.

ParentRowWriterLineage applies public edit_rows directly to prefixReads and
History before.checked. Constructor Valid for the initial heap follows from
the supplied initial shared Ready and coherent.valid. The resulting pair
contains History start.checked and constructor Valid of that exact heap.
This use avoids the separate startValid field returned by lower row lineage,
which denotes EndpointMemoGateTrace.Valid for the global memo bundle.

The captured call is EditChildren over original.children, at offset zero,
from the same start to rowMiddle. childReads is indexed by that exact call
and threads rowMemos to rowFinal. Applying edit_children to childReads and the
pair from edit_rows therefore gives History rowMiddle.checked. No alternative
state, alternative inventory, or heap-only state reconstruction occurs.

Both adapters derive their history through actual read receipts. The row
adapter includes the raw makeEdge advance between earlier rows. The child
adapter follows the actual selected child calls. Ordinary constructor cases
use run_correct at the derived constructor Valid heap. Recursive head cases
use actual head effects. Leaf cases use actual Force/Target/native query
receipts and their checked traces. No arbitrary callee-history preservation
oracle or future query result is an input.

## Survivor and field retention

The lower proof identifies actual makeNode readback with canonicalEdges of
surviving rebuilt rows using coherent, linked, and resident facts derived by
rows_effects. It chooses one exact rebuilt occurrence and original source
index. Duplicate normalization can discard other occurrences. The index is
in the raw source and rebuilt lists; it is not a normalized row position.

The upper theorem retains that occurrence's exact full symbol and raw guard,
its ordered returned child list, and its actual makeEdge equation. It retains
the child's actual read graph. It also retains growth from start, rowMiddle,
and the row constructor's returned heap into the actual final node heap.
The final-reader growth facts are those already derived by the lower
node_survivor, including the final makeNode effect. They are not inferred
from the newly constructed histories.

Thus the claimed indexed-prefix and canonical survivor properties remain
sound. The theorem does not claim an occurrence bijection, unchanged row
order, or multiplicity preservation after canonical normalization.

## Exact boundaries

History here is SourceCurrentNativeEdgeWriterGrowth.History. It records
selected native edge writers and their actual earlier checked execution and
growth. It is not SourceCurrentNativeMuPublication.History, an outer active
owner history, or a semantic equivalence between child results.

The theorem supplies histories at row start and child-list return. The lower
children_indexed theorem still does not export a connecting earlier-children
prefix for the existential start of an individual selected child. The upper
theorem does not assert history at every such individual start. That separate
transport would need an indexed child-prefix receipt or an appropriate
induction through the actual child reads.

The upper theorem deliberately returns derived histories rather than the
lower prefixReads. Its actual child call indexes the same captured states,
so dropping that prefix witness from the result does not weaken the claimed
history linkage. A consumer that needs the prefix itself can use the lower
node_survivor with the same inputs.

This is a completed-edit provenance component. It does not construct edit
completion, an initial numeric schedule, general outer completion, a causal
well-founded rank, or exclusion of an outer busy node. Physical Grows alone
is not used as a replacement for history, issued-reference extension, or
SemanticReady transport.
