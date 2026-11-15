# Shared source preparation repair 1

2026-11-15 02:00:01 CET. Uncompiled.

The public theorem header remains byte-identical. The original input and failure log remain unchanged.

- Omit the three unused section instances from private `node_lookup`.
- Reduce the own-preparation result by reflexivity after simplification.
- Transport each PrefixValid proof to the concrete narrowed constructor first.
- Apply prefix_context and prefix_packet at that constructor. Their dependent result matches then reduce directly.

The last change avoids rewriting a dependent match that still contains its original validity proof. The real common-fuel coupling, actual narrowed parent and heap, original source inventory, Empty branch, zero stop, and actual shared scan remain unchanged. Read the original CASE for the complete scope and remaining child-dispatch operation.

No compiler, live source, Git, board, Haskell or /tmp changes.
