# Fallback forecast proof repair

Recorded 2026-11-15 02:29 CET. This packet is UNCOMPILED. Root owns all checks.

The combined60 check reported only two fallback diagnostics. Its forecast equality still contained the locally irreducible fallbackPlan. The proof now explicitly unfolds only fallbackPlan at that remaining equality and closes it by reflexivity. The runtime equation also removes the reported unused nextPoint simp argument.

The two original explicit theorem headers are byte identical. The original past-observation Origin constructor is byte identical. No premise, conclusion, reservation, forecast, budget, runtime definition, resource contract, or original full target changes. No linter is disabled. The other return-case diagnostics belong to the separate worker.

Use this repaired APPEND-FALLBACK-CHILD.lean.txt with the original constructor insertion. proof-only-repair.patch shows exactly the two proof edits against the prior append. The original packet's NOTES.md retains the complete scope and open cases. All four original targets, all prepared-row16 conjuncts, the full source induction, and the joint finite-witness goal remain in scope.

Probes remain identity_actual_source_fallback_child_current and identity_actual_source_fallback_child_rejected in MicroCFTA.SourcePruningEnumerationSharedEagerReservation. No compiler, live source, Git, board, Haskell, or /tmp write was performed.
