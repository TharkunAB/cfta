# Native callback history checkpoint

Proof commit: b9434f53991152fb0bcb319a077a792c67d20a02.
Starting checkpoint: 84f47113de1598e3bbdaaa694874c49684574193.
Source main: c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e, merged at 896b0a1c.
Status: PROGRESS. The whole-library goal remains active.

Read CONTINUE.md and lean/notes-current-native-callback-history.md for the
exact results and next proof. Read lean/notes-proof-status-20261017.md for
the whole-library contract and remaining boundaries. Root FINDINGS.md keeps
the current Haskell repair handoff before historical failure reports.

## Proof and validation

Four production modules add causal native publication histories, checked
step/trace history transport, actual callback row cleanup, and current
native construct readback. The optional completion producer uses initial
Ready, Available body, and causal History. The receipt retains the actual
current callbacks and selected complete earlier winner. If the binder is
unused, returned row origins equal the current raw ordinary callback rows.
The result does not identify them with the original pre-substitution body.

Selected evidence has 17 public declarations and four constructed checks.
These are 21 signature/axiom pairs in seven groups. All public groups print
complete proof terms. All groups use all eight explicit print/linter flags.
No selected probe log contains diagnostics, omitted terms, or sorryAx.
Only propext, Classical.choice, and Quot.sound are permitted. The four final
strict source logs are empty and match the frozen production hashes.
All four canonical targets pass.

The constructed checks cover a used pair with an actual nested Mu and exact
warm replay; unused native binding that returns the original live ordinary
row; a source-built nonidentical checked query with a protected returned
cell, causal selected unused-Mu law, and populated warm replay; and a
source-built recursive Mu/union completed checked query. They instantiate
the producers from their own initial source states. They do not establish
general recursive outer completion.

The full pinned Lean 4.34.1 Audit passes 3084 jobs and 67897 axiom-dependency
checks. Effective MemoryMax and MemoryHigh are both 4294967296 bytes.
Effective memory.swap.max is zero. The Audit peak is 383 MiB. All heavy
checks run through heavy-management with task-specific peak logs.
Canonical and Audit logs retain the existing unused-input warning in
InternedFreshOrdinaryClosedCompletion.lean:24. That frozen source is unchanged.
The new final source logs and selected probe logs have no warnings.

Three component manifests verify 117 file hash references. Root readback
sources and checks are covered by frozen-modules.json, selected groups,
checkpoint-validation.json, and the complete SHA256SUMS file. Failed
attempts retain their exact source snapshots, raw logs, and metadata.
These include the root normalization namespace typo and noncomputable
history declaration, plus the component proof and packaging attempts.
Five preserved probe or worktree snapshots end with a blank line. Git
reports those raw snapshot endings in its whitespace check. Production
sources and edited prose pass the whitespace check.

## Preservation and reproduction

verify-probes.py checks all selected public and constructed groups and the
four strict source snapshots. verify-checkpoint.py also checks canonical
builds, component manifests, caps, and the full Audit. Its output must equal
checkpoint-validation.json.

verify-preservation.py checks all 18701 starting files. It retains 3079
older non-Audit Lean sources, 242 Haskell files, 206 active-package files,
two stashes, three other worktrees, and 107 frozen module manifests with
841 hash references. The only prior proof-source edit adds the four
imports to Audit.lean. The existing Haskell repair registry and historical
findings retain their content. No new Haskell behavior patch is added.
The unchanged source reuses its strict Nix all-component build, 798 examples
plus golden, Fourmolu, and Cabal-gild validation.

verify-closure.py checks a clean committed worktree, every tracked blob and
mode, index equality, complete evidence checksums, and retained verifier
reports. With --remote-file it also checks the published formalize SHA and
source main. Save the final closure output outside this frozen directory
to avoid a checksum self-reference. Raw .log files are explicitly tracked.

Do not append new work to this evidence directory. Start a new evidence
directory and task-specific resource logs for the next proof.
