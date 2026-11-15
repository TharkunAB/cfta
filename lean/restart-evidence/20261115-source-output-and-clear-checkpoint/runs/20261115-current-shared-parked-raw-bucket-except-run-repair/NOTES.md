# Normalize the concrete restart list

Status: UNCOMPILED. The root agent owns validation.

The typed-Except private check reported one remaining error at line 181.
The local `exactRows` proof left `ExceptT.run` around a concrete singleton
list after unfolding the restart.

This repair adds `ExceptT.run` to that one `simpa only` list.
No other source byte changes. The inverse replacement restores the entire
previous source. The complete public header remains byte-identical.
Header SHA-256: 42188c744a3db349c91b17fca96ae01a3b55d8a76b9e81b3f0b62809319a7f10.

All input premises, conclusions, operation receipts, endpoints, and runtime
expressions are unchanged. No provider or linter setting was added.

Public candidate:

`MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive.parked_singleton_removed_bucket_receipt`

The original source and target audit remains in:

`lean/restart-evidence/20261115-current-shared-parked-raw-bucket-receipt-draft/NOTES.md`

The full original emitted-root finite completion and compatible assignment
target remains open. The earlier-entry historical connection remains open.
No Haskell defect or change was established.

No compiler, live source, Git, board, Haskell, child, or temporary evidence
was changed. Both failed original packets remain unchanged.
