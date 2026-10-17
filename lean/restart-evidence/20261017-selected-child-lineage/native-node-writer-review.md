# Native node writer history

Final production: `SourceCurrentNativeNodeWriterHistory.lean`.
SHA256: `723be146423a2da8b407fba55cdd2e86fcccb25cfdb56ea423c00b4dcbdfebf9`.
There are four public declarations and no new datatype constructors.

## Exact new result

The existing `SourceCurrentNativeEdgeWriterGrowth.History` is unchanged.
It records empty native tables, exact growing physical advances, and actual
completed checked traces. `writers` derives an earlier node writer for
every returned node cell in that history. It does not assume a stored
node-origin law. `warm` identifies the same complete captured NodeRequest
from actual memoized lookup and ready demand with physical validity.

`Written` retains the captured node handle and full request, Good and
NodeReady at the writer start, the actual compileNode trace to the literal
returned Value, the same evaluating owner at body return, the actual
one-step finishNode trace, and growth from both writer heaps to the reader.
`Written.grows` retains that receipt through later physical heap growth.
The whole result can be a Mu value. It is not identified with a recursive
body callback value, ordinary probe, erased value, or reconstructed result.

The producer uses strong induction on actual trace fuel. Actual node lookup
inserts only suspended cells. Demand changes only the selected suspended
phase. Every successful evaluate branch crosses its compiled body and
protected finish. The body-owner theorem prevents replacement of its
captured owner. Finish records the actual result under that same handle.
Work and optionalBinder use actual checked growth. Edge execution retains
node cells and includes any nested completed node writes. Physical advances
retain the entire node-cell function and supply actual past growth.
Clean controls exclude externally supplied finish instructions.

The proof reuses existing invariant and protected-prefix APIs. Its private
node-cell preservation proof follows the earlier frozen edge-cell proof.
That private duplication avoids changes to the older immutable module.
No generic desired-writer predicate is exposed as a producer premise.

## Boundaries

This is past-execution provenance, not an initial completion theorem.
The current Good and key safety premises identify the exact warm request.
There is no Original, NoDeep, finite Cap, or whole-forest closure premise.
The key can name generated operands when the actual checked request permits it.
Constructor handles remain distinct from the issued-name ledger.

Written records the literal internal writer states. It does not package
History at that internal start or a global root-prefix embedding. The start
can already contain active ancestor owners. A direct application of an
edge-history consumer inside the compiled body still needs an internal
prefix bridge or a retained-cell argument at the final reader. This module
does not claim full historical Leaf row provenance, retained-Mu alignment,
a well-founded row measure, all-active node exclusion, or outer termination.

## Constructed check

The private setup is copied from the frozen source
`20261017-active-row-progress/writer-child-kernels-6.source.lean`.
It builds its own ordinary leaf and productive Mu source. The cold checked
edge trace performs two actual native node self-queries, then publishes its
row. A later actual edge allocation increases the physical edge counter.
The fixture derives Good and History from those actual source operations.
It then proves both complete captured node requests hit the same handles,
both earlier writer receipts, and the two literal one-step warm traces.
It takes no supplied future history, trace, result, or writer law.
The native self-query returns the whole Mu without unfolding its callback.
This check therefore does not test Mu reconstruction or body equality.

## Validation

Strict direct-3: exit 0, actual raw log length 0 bytes.
Canonical-1: exit 0, 1169 jobs. It replays only the unchanged old
ClosedCompletion unused-input warning. The new source has no diagnostic.
Public-1: four full explicit signature, proof, and axiom groups.
Kernels-1: one full constructed group. All eight printer options are present.
Selected outputs contain only propext, Classical.choice, and Quot.sound.
No selected output has a printer failure, omission, sorryAx, or warning.
Effective cgroup Max and High are 4294967296 bytes; SwapMax is zero.
All failed numbered source and raw log attempts remain immutable.
No older production, Audit, Haskell, or authority document was changed.
