# Filter seeded native entry: heap transport repair

Recorded: 2026-11-14 21:41 CET.

This new packet preserves every earlier packet. It repairs only the final
seed projection and its native-call transport. No compiler, live module,
Git, board, Haskell, original target, or theorem premise was changed.

Source SHA256:
`29dd18d73998499fa0f6c2a130382067553df096629b875ae378b8b85fd43d75`.

The remaining strict log is
`20261114-prefix-resources-and-zero-publication/filter-index-2.txt`.
All constructor patterns and the first publication helper now elaborate.
The remaining errors concern the projected heap and cleared variable names.

The replacement expands the actual `advancePhysical` and native `advance`
definitions when transporting the seed graph. The physical heap projection
then equals the actual `projectedHeap` supplied to the advance.

Projection uniqueness now produces named `goalSame` and `heapSame` equations.
The proof rewrites those equations only into the native trace. It retains the
original `goal` and `projectedHeap` names. A new local `nativeCall` proof
normalizes the two literal advances to the same actual checked state.
No machine, native table, equality cache, domain, operand order, or returned
endpoint is substituted.

Both public raw headers and the private publication header are byte-identical
to the previous packet. The source remains uncompiled and requires root's
strict checks. No Haskell fix was found.

The original scope note still applies. The source visitor is not proved to
reach this particular seeded graph. The actual suspended descendant query
can use different values and paths. Whole allocated-edge/native
correspondence and the full finite-compatible-completion goal remain open.
