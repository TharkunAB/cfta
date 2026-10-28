# Exact new-worker stopping certificate — OPEN

The old HookCertificates.StoppedAt takes a Stop whose reason is the concrete old Recursive.Failure. ReceiptAt and OutputAt do not have that dependency. Rebinding only Failure in the sibling producer would therefore be ill-typed at the stopping certificate.

The new PreparedHookCertificates draft defines PreparedStoppedAt and its prepend lemma. It changes only that failure-type binding. It retains the literal unsupported .unhandled branch and actual exhausted continuation branch. The latter retains the same current completed receipt, selected variable, metadata, callback cache, optional native endpoint, ReceiptAt facts, and own Packet. No stop is dropped or weakened.

The immutable v2 PreparedHookResources draft explicitly uses PreparedStoppedAt and new PreparedRecursive Failure/continueWith/resume. Its leaf is receipt_zero_complete_prepared. The entire v1 declaration is recovered after the explicit PreparedStoppedAt-to-StoppedAt text inverse; namespace/type bindings are recorded separately. Version 1 remains intact, along with Root's actual strict PASS source/report/raw. Its original old-callback theorem is not silently relabeled as a new-worker result.

No positive-depth recursive completion or new-worker Complete IH is supplied by these base-case drafts. The separate prepared finite-head theorem still explicitly requires and executes the old positive Complete/resume. Proof drafting stops after this bounded zero-worker connection.
