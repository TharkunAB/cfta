# Actual new worker zero callback — OPEN

The new immutable draft `SourcePruningEnumerationPreparedCallbackZero.lean` proves the zero callback contract in namespace PreparedRecursive. Its Packet and Output are the original explicit old types. Its Failure, continueWith, and resume are the actual new worker types and functions.

It invokes old Recursive.callback_complete once. That producer fixes actual fuel, Bool/metadata result, core, Packet, RenderStable, Frame, and type/hole/typing fields before every larger-fuel execution. The new proof uses the actual recordTypes singleton row. It unfolds the new continueWith and cases the returned pair and Bool to prove its own continuation equation. It does not use the old typed continuation equation. The same new zero resume then yields exact pruning, stop-rule output, done output, stuck empty output, or exhausted failure. Native Caller and query endpoints remain the original ones in every case. No model, future success, or new recursive IH is an admission.

The entire old 4,162-byte theorem declaration text is retained. Its namespace and explicit type bindings now refer to the new runtime. This is an intentional semantic binding change, not literal old/new runtime equality.

The small `SourcePruningEnumerationPreparedReceiptHook.lean` adapter uses this new leaf for a completed actual receipt. The actual complete receipt derives its own Packet from original admission, Pending, FragmentHistory, and Post. Handled rejected/stopped receipts keep the exact empty continuation. Unhandled receipts contradict the supplied actual advance. It retains the old receipt-level declaration after theorem-name inverse and uses new failure/runtime bindings.

Both drafts are UNTESTED until Root supplies actual compiler receipts. Their resource scope is zero recursive expansion. No positive-depth completion or arbitrary-hook completion follows from these drafts alone.
