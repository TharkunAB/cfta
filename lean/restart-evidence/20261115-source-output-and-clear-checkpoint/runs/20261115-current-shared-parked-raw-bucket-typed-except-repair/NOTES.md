# Typed Except repair for the parked bucket receipt

Status: UNCOMPILED. The root agent owns validation.

The previous private check reported only two invalid dotted `.ok` terms in
`exactRows`, at lines 178 and 179. Their local equality supplied no expected
Except type before the constructors were elaborated.

This repair qualifies both constructors as `Except.ok`. It specifies
`ε := EnumerationState.Error` for both constructors. That parameter name was
checked against the installed Lean 4.34.1 `Except` declaration.

The complete public header is byte-identical to the original packet.
Header SHA-256: 42188c744a3db349c91b17fca96ae01a3b55d8a76b9e81b3f0b62809319a7f10.
All premises, conclusions, operation receipts, endpoints, and runtime
expressions are unchanged. Only this local proof equality changed.
The inverse block replacement restores the complete original source bytes.
No linter setting, premise, or provider was added.

Public candidate:

`MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive.parked_singleton_removed_bucket_receipt`

The source and target audit remains in:

`lean/restart-evidence/20261115-current-shared-parked-raw-bucket-receipt-draft/NOTES.md`

The full original emitted-root finite completion and compatible assignment
target remains open. This receipt identifies one actual cleared raw bucket
and direct shared restart. The earlier-entry historical connection remains
open. No Haskell defect or change was established.

No compiler, live source, Git, board, Haskell, child, or temporary evidence
was changed. The failed original packet remains unchanged.
