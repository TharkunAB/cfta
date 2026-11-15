# Shared source preparation repair 3

2026-11-15 02:16:00 CET. Uncompiled.

The only change copies enterAtZero to enterLiteral and rewrites its reached heap projection with reachedHeap. nativeAtZero then uses enterLiteral. The normalized entry equation matches the normalized native call. The original entry equation remains available.

The full public header, real common fuel, actual narrowed parent and heap, source inventory and all other proof sites remain unchanged. Earlier frozen inputs and logs remain unchanged. No compiler, live source, Git, board, Haskell or /tmp changes.
