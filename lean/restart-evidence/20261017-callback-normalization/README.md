# Callback normalization and causal native histories

Starting checkpoint: `430332f6fd3267c7d40196a914275b57aab0c37f`.
Proof commit: `c86f75c04156d65c53f43bbebedd8efb4e7c4d6d`.
Source main: `c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e`.
The upstream pull passed before this work. Only formalize is published.

Read `lean/notes-current-callback-normalization.md` for the theorem boundaries.
Read `lean/notes-proof-status-20261017.md` for the whole-library target.
General nested callback comparison, recursive outer progress, repeated-pass
convergence, and complete current Haskell correspondence remain open.

The 12 production modules have empty final strict source logs and passing
canonical targets. Audit passes 3063 jobs and 67649 dependency checks.
Its actual limits are 4 GiB MemoryMax, 4 GiB MemoryHigh, and zero swap.
Its recorded peak is 375 MiB. Audit replays one earlier unused-input warning
from InternedFreshOrdinaryClosedCompletion. It adds no new source warning.

There are 38 new public declaration checks and 8 constructed checks across
10 selected groups. Definitions are included in the public count. Each
public declaration has its complete signature, proof or definition, and
axiom report. Every selected source sets all eight required printer and
linter options. Selected imported logs contain no diagnostics, sorryAx,
omission markers, or truncated output. Only the three standard axioms occur.
`selected-groups.json` identifies each final group exactly once.

The constructed checks cover singleton self, ordinary merging and warm
replay, discarded colliding captures, actual fresh reservations beside an
open Mu, accepted and sentinel cold-to-warm edge requests, complete actual
Parent reduction, and used nested optional construction followed by bounded
recursive editing and Local calls. The edge examples contain a constructed
productive Mu, but their selected walks are nullary or arity mismatches.
They do not prove recursive Mu execution. Later bounded editor and Local
checks retain the invariant without asserting successful completion.

All failed attempts and terminated runs retain their source snapshots and
raw logs. Root kernels 2 and 3 were stopped after known elaboration errors.
The final root kernels 5 pass. No failed run counts as selected evidence.
Raw whitespace is retained and listed in artifact-whitespace.json.
The aggregate uses union-local-public-final-2. It adds only @ to the 18
original #check commands. The original component probe remains unchanged
and is not counted twice. Two failed aggregate checks retain their scripts
and logs. They found the printer-command form and a manifest field name.
Neither failure changes a production proof.

No Haskell behavior patch or new production defect is added. Root FINDINGS
keeps current repair status first. Field-pool repair b9219b9e is merged and
validated. The unchanged source reuses its strict Nix build, 798 examples
plus golden, Fourmolu, and Cabal-gild checks. The original Chain reproducer
returns Left (FieldAtomOnDatatype "Next" 0).

Run verify-checkpoint.py to check final source hashes, selected probes,
effective caps, Audit, and component manifests. Run verify-preservation.py
to check all starting files, older proof manifests, Haskell sources, stashes,
other worktrees, and the retained Haskell repair registry. The baseline has
17619 files, 3050 earlier non-Audit Lean sources, 242 Haskell files, and
206 active-package files. All 105 frozen module manifests retain their
820 hash references, including this checkpoint's 12 modules.

SHA256SUMS covers every file in this directory except itself. After commit,
verify-closure.py checks filesystem, index, HEAD, file modes, all checksums,
and reproducible validation reports. Its optional remote-file argument
also checks the published formalize tip and the unchanged main tip.
