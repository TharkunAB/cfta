# Independent review of current required-path capstones

Reviewed 2026-10-16 08:27 CEST. No material proof or model defect found.

## Actual trace and state

`scan_required_memos` uses one actual current `ConjunctionClassScan.Scan` with outcome `none` for both `ScanReads` and required completion. The required worker starts at that Scan's exact returned heap. Its actual done equation comes from the derived stable bound. No completed required-worker callback is supplied. The returned `Receipt` retains both complete native tables, the domain cache, and the equality operation state. Its effects retain loaded fields and its inventory admission is derived through the actual constructor effects.

The three global tables pass from initial `memos` to `scanMemos` through the actual Scan receipt, then to `finalMemos` through actual required head/child/row receipts. The theorem proves unfolding extension and exact retention of both query tables during required execution. It does not claim that the preceding Scan leaves those query tables unchanged.

`records_required_memos` derives positional `Retained` from that same actual Scan over `records.map Record.paths`. It preserves literal head occurrences at selected branches. Order and multiplicity follow the receipt and Sublist. Equal path fields do not imply unique original records. Coherence, ascending tries, and nontriviality transfer from the original record premises. All selected path domains and exact required-filter language remain available in the returned Receipt.

## Actual allocated entry

`AllocatedRequired.finite` derives the current Scan from initial invariants and reached range checks. No completed Scan or required worker is supplied. Its original allocation History, cache validity, expression guard coverage, actual original construction equation, and resident edge remain explicit. It obtains the actual field load and normalized readback from these premises. A successful actual precheck supplies proper active records. The empty-root inventory admission is derived internally from the literal cold native state.

The prefix state retains `finalCache` inside the equality operations and retains the exact returned precheck operation state. Native memo/domain tables and operation tables are model-initialized at this entry. This is not a statement that the Haskell process resets its global tables or equality interner. Initial fourth-memo correctness and three-table validity remain explicit; the kernel specialization derives fourth correctness for the empty table.

The stopped branch refutes an original class on each accepted original forest. The successful branch keeps the SAME actual Scan proof in `Retained` and `ScanReads`, then derives required execution. It does not claim result-language correctness of later class edits or the complete outer constrained caller.

## Source scope and remaining boundaries

Current `Equality/Operations.hs:206-226` tests contradiction first, scans refused classes with primary and secondary short circuits, and applies `requireAll` only after the scan succeeds. `:279-303` defines the literal needed-path worker, including head exposure, selected children, and edge filtering. These capstones preserve that successful-prefix division. Completed resident unfolding receipts do not establish a GHC lazy demand order, pending publication behavior, native Map/IntMap representation equivalence, or all outer caller effects. Unrelated open siblings are permitted by the generic required endpoint; no whole-forest ClosedValues premise is introduced.

No frozen proof source, Haskell file, Audit, documentation file, or Git state was changed by this review.
