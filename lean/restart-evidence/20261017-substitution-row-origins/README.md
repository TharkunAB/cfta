# Stored substitution row origin checkpoint

Proof commit: a4b6e12d948f44142e5d982e00cf8935efb93884.
Starting checkpoint: 89a9a5125e02760cf1ed939614219abd81497820.
Source main: c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e, merged at 896b0a1c.
Status: PROGRESS. The whole-library goal remains active.

Read CONTINUE.md and lean/notes-current-substitution-row-origins.md for the
new results and exact remaining target. The full proof map is in
lean/notes-proof-status-20261017.md. Root FINDINGS.md keeps the Haskell
repair handoff first. CONTINUE-initial.md preserves the earlier handoff.

## Proof and boundary

Five production modules derive independent capture-plan equivalence,
actual ordered encoded row calls, each child's literal stored substitution,
node/union row origins with initial completion, and a checked boundary.
The Calls relation retains the original replacement environment, each
child's own leaves, and exact prefix/suffix heaps. Node normalization maps
an output to an existential source/rebuilt occurrence. It need not preserve
row numbers or give a unique or injective map. Guards, symbols, and arity
are exact. Union origins concern actual substituted member returns.

Initial semantic heaps, coverage, and source/replacement availability
construct the actual node and union returns, row receipts, and causal
histories. Closed roots return unchanged. Nested Mu children are allowed.
The general retained-Mu recursive source relation remains open.

The checked boundary builds a closed used outer Mu containing an unused
raw inner Mu that captures the outer name. Actual stored self rebinding
smart-erases that inner wrapper. The result differs physically from the
original ordinary probe. The same fixture retains root symbol/full guard,
arity, and the ordered child relation after an exact repaired inner unfold.
This is a formal correspondence boundary, not a new Haskell defect.
The two-reconstruction equality in the review is proposed and unproved.

## Validation

Full pinned Lean 4.34.1 Audit: 3089 jobs and 67978 dependency checks.
Effective MemoryMax and MemoryHigh are both 4294967296 bytes; swap.max=0.
Audit peak: 367 MiB. Every heavy check uses heavy-management and task-specific
peak logs. All five final source checks are empty and match the frozen
production hashes. All canonical targets pass.

Selected evidence contains 27 public declarations and 6 constructed checks:
33 signature/axiom pairs in 9 groups. Public groups print complete proof
terms. All selected groups explicitly set all eight required options.
No selected log has diagnostics, omitted terms, or sorryAx. Only propext,
Classical.choice, and Quot.sound occur. Boundary public printing references
its checked private construction proof to avoid expanding a large reduction.
Canonical and Audit logs retain the frozen ClosedCompletion:24 unused-input
warning; new source and selected probe logs have no warnings.

Constructed checks cover shifted/duplicated capture contexts with nested
raw Mu, nearest-local shadowing, reversed changed-child replacements,
initial node and union completion with a nested raw Mu, and the boundary's
exact row fields and actual inner unfolding. Three component manifests
verify 158 file hash references. Root source/probe snapshots are covered
by frozen-modules.json, selected groups, and complete SHA256SUMS.

Failed attempts retain their raw snapshots, metadata, and logs. Boundary
public1 returns zero but reports a pretty-printer failure; it is unselected.
Boundary public2 is terminal -15 and unselected. Final public3 is clean.
All earlier source, integration, and packaging attempts remain preserved.
Six preserved raw snapshots or logs retain whitespace reported by Git.
The production sources and edited prose pass the whitespace check.

## Preservation and reproduction

verify-probes.py checks all selected pairs and final strict snapshots.
verify-checkpoint.py also checks production hashes, canonical targets,
component manifests, effective caps, and the full Audit. Its output must
match checkpoint-validation.json.

verify-preservation.py checks 18858 starting files, 3083 older non-Audit Lean
sources, 242 Haskell files, 206 active-package files, 2 stashes, 3 other worktrees,
and 108 frozen module manifests with 846 hash references. It checks the exact
five Audit imports and keeps the Haskell repair registry first. The current
Haskell source is unchanged and reuses its strict Nix all-component build,
798 examples plus golden, Fourmolu, and Cabal-gild validation.

verify-closure.py checks every tracked blob/mode, index equality, a clean
committed worktree, all evidence checksums, and retained verification
reports. With --remote-file it also checks the published formalize SHA and
source main. Save final closure output outside this frozen directory to
avoid checksum self-reference. All raw .log files are explicitly tracked.
Start a new evidence directory for later work.
