# Selected-clear cycle repair v2

Status: UNCOMPILED. The original strict check failed. Both axiom reports contain sorryAx. They provide no checked theorem credit. The original instrumented source, full diagnostic and earlier148-line source draft remain separately pinned. Prior owners remain unchanged.

The actual line93 failure is in the final semantic conclusion. The SameClass proof does not need a repair. The original first header parsed its final clause as `(membership -> meaningAfter) <-> meaningBefore`. It therefore required an unrestricted old-slot meaning outside the listed vertices. This is stronger than the intended listed-vertices statement and cannot follow from the original inputs. Treating the failure as another binder-introduction issue would conceal a statement error.

Root explicitly approved this correction after the diagnostic review: `vertex ∈ vertices → (slotAfter ↔ slotBefore)`. The candidate adds exactly those two parentheses in the first header. It adds no hypothesis or provider. Every original input, the first two conclusion clauses and the complete second theorem header remain byte-identical. The private helper and preamble remain byte-identical.

Two proof repairs address the remaining actual diagnostics. The slot-lookup simp retains only the argument used in the failed check. The positive path-length proof uses constructor cases and Nat.zero_lt_succ instead of the unavailable List.length_pos.mpr. No other proof code changes.

HEADERS.json retains both full old and corrected headers. CHECKS.json records their hashes, the approved difference, exact preservation checks and forward/reverse unified-patch replay. The old false header and sorryAx reports remain failures. Root must check the corrected source before assigning proof credit.

No compiler, evaluation/runtime job, live source edit, Git, board or Haskell action ran. No Haskell fix was established. This is a correction to an unproved local Lean draft.
