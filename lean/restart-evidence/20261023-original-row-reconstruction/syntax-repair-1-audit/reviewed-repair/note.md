# Syntax-only repair proposal

Strict1 used the original 210-line source. It exited 1 with two parse errors and no warnings.
The errors are at multiline native record-field expressions in the private and public headers.
This repair adds parentheses around all three matching `advance` applications, including the body expression.
Deleting exactly those six parentheses recovers the failed source byte for byte.
The context and all eight local type fragments remain unchanged.
The private and public headers change only by the same parentheses. Their complete new contracts are in `signature-repair`.
The source remains 210 lines, with one private helper and one public theorem.
The previous source, complete actual failure evidence, original signature, and exact patches are retained.
No new premise, field, helper, option, limit, or mathematical behavior is added.
This proposal is uncompiled. Root and independent source review must precede any next check.
No prepared tool, compiler, runtime, Git, network, board, or repository write was used.
