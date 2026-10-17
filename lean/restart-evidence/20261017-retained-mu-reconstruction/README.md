# Retained Mu reconstruction checkpoint

Proof commit: 7a441d2d55cc7a8db3868a70cf0e5dd605300d1d.
Starting checkpoint: 5ce4cca1d523f4d4724e4e79b66a6ddfb7c50c17.
Source main: c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e, merged at 896b0a1c.
Status: PROGRESS. The whole-library goal remains active.

Read CONTINUE.md and lean/notes-current-retained-mu-reconstruction.md for
the exact result and next producer. The whole-library proof map is in
lean/notes-proof-status-20261017.md. FINDINGS keeps the Haskell repair handoff
first. CONTINUE-initial.md preserves the earlier work-in-progress state.

## Results and boundaries

Six production modules construct both selected-Mu reconstructions and their
common-final replays, retain actual causal writer growth, and define open
observations through actual Mu unfolding. Source paths cover all stopping
outcomes. Selected writer readback keeps the original first writer through
later warm reads and discarded candidates. Both original raw callback heaps
grow into the actual reader heap.

Open observations retain references, exact full guards and symbols, and
ordered child relations in a fixed epsilon view. They do not claim row
multiplicity, order, identity, or transport to another heap. Four-table
Grows does not state issued-reference extension. NoNewMu alone gives neither.

Forty finite trials complete with equal result references. Two constructed
kernels prove full Value equality with actual source and history premises.
General reconstruction equality and retained-used Mu row congruence remain
open. General outer progress, convergence, current frontend/runtime adapters,
and complete Haskell correspondence remain open.

## Validation

Full pinned Lean 4.34.1 Audit: 3095 jobs and 68057 dependency checks.
Effective memory.max and memory.high are 4294967296; memory.swap.max is zero.
Audit peak is 376 MiB. All heavy jobs use heavy-management and a task-specific
peak log. All six final strict source logs are empty. Canonical builds pass.

Selected checks contain 37 public declarations and eight constructed checks:
45 signature/axiom pairs in nine groups. Every new public proof prints
completely. Selected logs contain no diagnostics, omitted terms, or sorryAx.
Only propext, Classical.choice, and Quot.sound occur. The canonical and
Audit logs retain the older ClosedCompletion unused-input warning. No new
production or selected probe log has a warning.

Constructed checks cover source-built nested Mu, an actual pending owner,
complete productive Mu unfolding, the bare-reference observation boundary,
writer growth at a common reconstruction heap, and two full-value examples.
The executable forty-case grid is finite evidence, separate from the kernel
proof pairs. Four component manifests verify 181 file hash references.

Earlier failed attempts keep their raw source snapshots, metadata, and
diagnostics. Read component reviews and root-review.md for exact corrections.
No preserved diagnostic or failed snapshot is counted as a final check.

## Verification and preservation

verify-probes.py checks selected signatures, complete public proofs, allowed
axioms, effective limits, and final strict source hashes. verify-checkpoint.py
also checks canonical builds, component manifests, and Audit. Its output
must equal checkpoint-validation.json.

verify-preservation.py checks 19082 starting files, 3088 older non-Audit Lean
sources, 242 Haskell files, 206 active-package files, two stashes, three other
worktrees, and 109 frozen module manifests with 852 hash references. It
allows exactly the six new Audit imports and declared documentation updates.
The Haskell source is unchanged. Its earlier strict Nix build, 798 examples
plus golden, Fourmolu, and Cabal-gild checks still apply.

verify-closure.py checks every tracked blob and mode, equality of filesystem,
index, and HEAD, a clean committed worktree, all evidence checksums, and
the retained validation reports. With --remote-file it checks the published
formalize SHA and source main. Save closure output outside this directory.
All raw logs are explicitly tracked. Start a new evidence directory for
later work. Never edit a frozen source or evidence file after publication.
