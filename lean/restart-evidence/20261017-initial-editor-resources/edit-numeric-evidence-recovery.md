# Evidence name collision and recovery

Recorded 2026-10-17 11:26 CEST.

The other proof owner wrote its generic integration under the reserved
`edit-numeric-kernels` prefix. It replaced the live source and attempt 1
source and log. The other owner has copied those generic files to its own
`node-owner-integration` prefix. Production sources did not change.

Concrete source snapshots 2 through 8 remain intact. Attempt 8 contains
the complete concrete Node theorem. Its log has only three noncomputable
definition errors. The subsequent intended attempt 9 correction read the
foreign live source. Therefore attempt 9 validates only that generic source.
Attempt 10 also used the foreign live source and failed to find the concrete
compiled theorem. Neither log validates the concrete integration.
The replaced live source also remains in `edit-numeric-collision-live.source.lean`.

The original attempt 1 full raw log is unavailable. It is not replaced by a
later run. The recorded tool output identifies two original errors: the
open-parent inequality needed an explicit contradiction, and the Cap proof
could not rewrite the row children through its alias. The separate
`edit-numeric-original-attempt-1.reconstructed.lean` reverses the known
attempt 2 patch. It is a reconstructed source, not an original snapshot.
The files currently named `edit-numeric-kernels-1.source.lean` and
`edit-numeric-kernels-1.log` contain the foreign generic attempt.

New concrete checks restart at attempt 11 from the intact attempt 8 source.
They mark the three size-based definitions noncomputable. New final metadata
will name only the final concrete success log as validation. It will preserve
all collision files and failed logs as historical evidence.

Attempt 11 re-established the concrete Node theorem from its immutable
source. `edit-numeric-kernels-11-immutable.log` is its direct strict check.
Attempts 12 and 13 add the compiled forest proof and fail in its local
selected-index proof. Attempt 14 checks both complete concrete kernels at
`edit-numeric-kernels-14.source.lean` and succeeds without diagnostics.
The restored live file equals that immutable attempt 14 source.
Attempt 6 records an incorrect Lean input path. Its captured error is a
repeat of that invalid invocation; it does not validate the source snapshot.
No claim states that every current raw attempt survived the collision.
All older baseline and previously frozen component files remain unchanged.
