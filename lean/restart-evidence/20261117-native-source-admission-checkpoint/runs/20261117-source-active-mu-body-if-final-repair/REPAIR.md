# Body and Boolean reduction repair

Status: UNCOMPILED. Original fb14/check95866 failed with exactly10 diagnostics. It reached37 reports but recovery used sorryAx. It has no full363 credit. The original packet and diagnostic log remain immutable.

The new proof changes only the reported sites:

- Add the literal universe-body reduction next to sameBody. This normalizes both child operands without unfolding the generic left-body match first.
- Use default simpa with bodyShape at the four mixed row/union call sites. The default simplifier removes their literal true/false conditionals. The other compiler proof sites are unchanged.
- Replace ineffective clear with an explicitly constructed local conjunction of the retained operationsValid, wholeBound, wholeActual, inputs and fields admissions. The syntactic proof does not need these assumptions. Their original names/types and the full public contract remain exact. This local term references them without adding a premise or a theorem.

Checked654 prefix, every private header, full public363 header/declaration, and all probes remain byte exact. Expected counts:37 theorem reports and4 declaration checks. No proof limit, linter, execution fuel, endpoint or source assumption changes. No Source/compiler/Git/board/tmp action occurred. Full363/441e and one finite accepted completion remain open pending validation.
