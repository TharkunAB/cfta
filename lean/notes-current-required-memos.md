# Actual global memo effects through required execution

`SourceCurrentRequiredQueryMemos` records the actual completed required
worker. HeadReads contains its bounded exposure calls. NodeReads,
ChildrenReads, and RowsReads follow the actual graph in source order.
Unselected children and rejected rows add no calls. Constructors retain
the current tables. No source predicate call is added by the receipt.

Each public memo theorem starts with an actual completed graph, semantic
readiness, the stored cost invariant, available inputs, and valid initial
global tables. It derives the ordered receipt, final three-table validity,
retention of earlier unfolding entries, and equality of the query record.
No closedness, future invariant, or supplied result receipt is required.

`requireAll_memos` uses literal bounded-worker success. RequireAllReads
contains the actual RequireChildren graph for the compiled Needed entries.
It retains the caller's original values and actual returned heap.

`SourceCurrentClassRequiredReady.scan_required_ready` composes ScanReads
with RequireAllReads at the actual scan-final heap. Constructor retention
also transfers the separate fourth emptiness memo. The native state uses
advanceHeap, so its warm operation tables are retained.

The unfolding extension in the theorem starts at the scan-final global
tables. Do not claim an initial-to-final extension without a separate scan
extension theorem. The scan and required receipts are actual ordered reads.

The theorem assumes a successful Scan. It does not prove general scan or
outer-caller termination. Later shared targets, edits, fallback merge and
subsumes operations, their separate merge memo, GHC demand, and publication
remain open. The full aggregate audit checks the new composition.
