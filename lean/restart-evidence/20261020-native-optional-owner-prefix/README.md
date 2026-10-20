# Actual captured native optional owners

Proof checkpoint: `db94389dc115be902e14e9c8f1bdf5b87af0e1f3`.
Starting checkpoint: `bfce6c47157e1178c53e622b637e9464b860dc99`.
Main remains `9769fe3e921d63836a0be337f19edd3c601f076e`.
The full-library goal stays active.

Read `lean/notes-current-native-optional-owner.md` for the proved claim,
validation, example and remaining obligations. Read
`next-owner-ancestry-handoff.md` for the next proof target.

The selected scope has nine modules, twelve public declaration readbacks
and one constructed readback. All ten selected strict logs are empty.
Default audit: 3504 jobs and 74153 axiom checks. The 62 capped commands and
17 failures include one missing-source build before Lean. Sixteen failures
are elaboration failures. Two successful style-warning attempts are retained
but unselected. Review receipt copies do not add jobs. The auxiliary key
snippet is included in command totals and excluded from official pair totals.

`verify-probes.py` checks full statements, proofs, standard axioms, selected
strict sources and actual memory limits. `verify-checkpoint.py` also checks
the proof commit, component manifests, current source/document ranges and
default audit. `verify-preservation.py` checks the starting files, all older
frozen manifests, Haskell files, active packages, stashes and other worktrees.
`verify-closure.py` requires a clean committed tree and compares every tracked
blob and mode with both the index and HEAD. It checks the sealed evidence.

Run the finalizer and closure under the required heavy-management cap.
Publication, remote readback and final closure records remain outside the
sealed directory to avoid changing their own hashes.
