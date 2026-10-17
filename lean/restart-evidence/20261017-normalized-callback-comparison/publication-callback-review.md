# Actual raw calls before Mu publication

The source is `SourceCurrentNativeMuPublicationCallbacks.lean`.
Its SHA256 is `fcf760e62065456344180f8edcc4495a784006c73d087d06d47ab0f2a26b0395`.
The earlier MuPublication and RequestWinner sources remain unchanged.

`callback_raw` extracts the actual raw build value and heap from any
successful repaired callback. It retains the exact filter pair. It uses no
semantic, completion, or result comparison assumption.

`contexts` derives the source `Context` at the actual ordinary callback
entry, the pre-reservation state, and the reserved body callback entry.
Each `Context` includes the historical `DepthHeap`.

`raw_callbacks` derives both raw ordinary and raw reserved build equations,
the exact subsequent filter pairs, and physical growth from both raw return
heaps to the actual `afterBody` heap before publication. It also returns the
two callback entry contexts. It uses the actual publication's source context,
callback equations, and reservation. It assumes no output comparison law.

Strict attempt 2 has an empty log. Its immutable source matches production.
Canonical attempt 1 passes 272 jobs. Public attempt 1 checks all three public
theorems with all eight explicit printer/linter options, complete signatures,
proof printing, and axiom printing. Only the three standard axioms occur.
All selected jobs read back 4 GiB / 4 GiB / zero swap.
Failed strict attempt 1 remains at its original source and raw log paths.

These are decomposition and transport results for an actual produced
publication. MuPublication constructs those events from full source
execution. This module does not derive unused-Mu normalized equality.
No additional constructed scenario is counted for this small helper.
