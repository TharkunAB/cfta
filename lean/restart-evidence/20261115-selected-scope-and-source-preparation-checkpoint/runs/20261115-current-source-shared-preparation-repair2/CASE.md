# Shared source preparation repair 2

2026-11-15 02:09:59 CET. Uncompiled.

The public header remains byte-identical.

- Omit only the unused Symbol and Node instances for private source_row_own_first.
- Prove the literal reached heap projection by reflexivity. Use it in nativeAtZero.
- Normalize only the local reached/caller aliases in a copy of preparedAtWork. Use that equation in the shared-policy simplification.

The prior shared-policy simplification did not match the prepared caller aliases. Its four unused arguments came from that missed rewrite. The replacement preserves all actual caller, heap, parent and common-fuel expressions. No source operation is replaced.

The original CASE states the complete scope and remaining child outcome. Earlier frozen packets and logs remain unchanged. No compiler, live, Git, board, Haskell or /tmp changes.
