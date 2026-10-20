# Final plain-owner fixture revision review

Reviewed at 2026-10-21 01:33 CEST. No material issue was found. This review owns zero Lean jobs and zero proof pairs. It reuses final strict5 and FULL public2 receipts.

Final source SHA256 is 489e43cb252d163470c9a1697eab4f84fee85c4c5cf205875a040470f52d64c2. The complete public type is byte-identical to the previously reviewed 5f2970b6 source. All source definitions and all earlier helper proofs remain unchanged. The only added helper, computed_receipts, proves the same three facts that were computed inline: the inherited payload is Top, the active owner's edge request reads the ready row, and the owner cell remains evaluating at the selected dispatch. The public proof uses their projections. The sole generic dispatch application remains unchanged.

The actual cold edge call still creates the returned memo cell before node activation. The same warm edge hit occurs under that owner. The literal take1 walk completes slot0 before slot1. The public theorem retains all three generic conclusions: reached dispatch, reference inequality, and complete key inequality. It requires no future selected child or root return. The same leaf in both slots is explicit. No positive-own reconstruction, native query, global rank, or general completion is claimed.

The final strict raw log has zero bytes. The complete public2 log has 168263 bytes and prints #check @, full #print, and #print axioms. Its seven print settings and the strict linter command supply all eight required settings. It has no omissions, warnings, printer failures, or nonstandard axioms. Both reused jobs use pinned Lean4.34.1, memory max/high4GiB, swap0, and a five-minute wrapper with fresh usage receipts.

The older strict/public attempts and both prior frozen review packages remain unchanged. In particular public1 is unselected and incomplete. Its -15 status alone supplies no established cause. This small revision review claims only the selected final receipts. Local snapshots make verification portable. --live --root ROOT also checks current repository bytes.
