# Stored alpha reconstruction and node congruence checkpoint

Proof commit: df79f8029ba227fbf773405883d5ce96435088d9.
Starting checkpoint: d3486d3bd925db4a06fa8ef1c327735ce038ed99.
Source main: c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e, merged at 896b0a1c.
Status: PROGRESS. The whole-library goal remains active.

Read CONTINUE.md and lean/notes-current-mu-congruence.md for the exact
results and next producer. The whole-library map and top-level target are
in lean/notes-proof-status-20261017.md. FINDINGS keeps the Haskell repair
handoff first. CONTINUE-initial.md retains the earlier incomplete state.

## Results and boundaries

Five production modules prove pure stored Alpha plan equivalence, actual
row replay, node row-set congruence, initial stored-node reconstruction,
and open-observation constructor laws. Initial Ready and available captures
construct both node calls in sequence with one exact canonical Value.
The source supplies a pure structural relation, not a future result law.
Exposed node rows may differ in order and duplicate count. Nested children
retain ordered Alpha relations, including arbitrary nested Mu. Both stored
roots in the new adapter are open nodes. Sequential heaps can differ.

Actual source histories do not yet derive the normalized relation for every
retained Mu writer. Nested normalization, union filtering and merging, raw
unused Mu cleanup, and earlier warm writers remain open. Mixed unions retain
physical alternative order. Open observations alone do not imply physical
empty-child agreement. A used-local source can reconstruct to a bare
reference. Preserve these cases in the general row-correspondence proof.
General outer progress, convergence, frontend/runtime adapters, and complete
public Haskell correspondence remain open.

## Validation

Full pinned Lean 4.34.1 Audit: 3100 jobs and 68149 dependency checks.
Effective memory.max and memory.high are 4294967296; memory.swap.max is zero.
Audit peak is 364 MiB. All heavy jobs use heavy-management and task-specific
peak logs. All five final strict source logs are empty. Canonical builds pass.

Selected checks contain 25 public declarations and ten constructed checks:
35 signature/axiom pairs in 12 groups. Every new public proof prints
completely. Selected logs contain no diagnostics, omitted terms, or sorryAx.
Only propext, Classical.choice, and Quot.sound occur. The canonical and
Audit logs retain the older ClosedCompletion unused-input warning.
Five component manifests verify 213 file hash references.

The integrations include used nested Mu, independent capture layouts,
reordered and repeated rows, dead rows, two distinct open stored roots,
exact complete reconstruction values, bare references, and empty replacements.
Two exploratory evaluators did not finish. One reached its five-minute cap;
one was stopped after focused kernel checks completed. Both remain excluded
from selected success evidence. Failed proof attempts retain their raw
source snapshots, metadata, and diagnostics. Read root-review.md and the
component reviews for the corrections and exact boundaries.

## Verification and preservation

verify-probes.py checks selected signatures, complete public proofs, allowed
axioms, effective limits, and final strict source hashes. verify-checkpoint.py
also checks canonical builds, component manifests, and Audit. Its output
must equal checkpoint-validation.json.

verify-preservation.py checks 19313 starting files, 3094 older non-Audit Lean
sources, 242 Haskell files, 206 active-package files, two stashes, three other
worktrees, and 110 frozen module manifests with 857 hash references. It
allows exactly the five new Audit imports and declared documentation updates.
Haskell is unchanged. Its earlier strict Nix build, 798 examples plus golden,
Fourmolu, and Cabal-gild checks still apply. Field-pool repair b9219b9e remains
merged and validated; FINDINGS records its rejection behavior and reproducer.

verify-closure.py checks every tracked blob and mode, equality of filesystem,
index, and HEAD, a clean committed worktree, all evidence checksums, and the
retained validation reports. With --remote-file it checks the published
formalize SHA and source main. Save closure output outside this directory.
All raw logs are explicitly tracked. Start a new evidence directory for later
work. Never edit a frozen source or evidence file after publication.
