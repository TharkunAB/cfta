# Continue retained Mu correspondence

Status: PROGRESS. Keep the whole-library goal active.
Proof commit: 7a441d2d55cc7a8db3868a70cf0e5dd605300d1d.
Starting checkpoint: 5ce4cca1d523f4d4724e4e79b66a6ddfb7c50c17.
Source main: c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e.
Local source merge: 896b0a1c. Work branch: formalize.

Read NEXT-PROMPT.md, HANDOFF.md, and root FINDINGS.md. Read
lean/notes-proof-status-20261017.md for the whole-library target and gaps.
The exact current result is in lean/notes-current-retained-mu-reconstruction.md.
CONTINUE-initial.md is the preserved earlier work-in-progress note.

## Completed here

Six frozen production modules now provide:

1. Initial-data completion of arbitrary stored substitution and both selected
   Mu reconstruction calls, with Ready, availability, and causal histories.
2. Exact replay of both calls at their common final heap, with the original
   selected writer. No equality between their returned values is claimed.
3. Finite open observations that retain bare references, full row guards and
   symbols, and ordered children. Actual Mu unfolding preserves these
   observations at every depth in its exact entry view.
4. Causal publication paths that retain actual cache growth.
5. Actual source producers for these paths at every stopping outcome.
6. Exact selected first-writer histories and growth of both original raw
   callback heaps into the actual reader heap.

All six final strict source logs are empty. All canonical builds pass.
Full Audit passes 3095 jobs and 68057 dependency checks. The actual cap is
4 GiB MemoryMax, 4 GiB MemoryHigh, and zero swap. Audit peak is 376 MiB.
The selected evidence has 37 public and eight constructed checks in nine
groups. All public proofs print completely. Only standard kernel axioms occur.
All check processes are terminal. No check needs to be resumed.

The forty finite reconstruction trials all complete with matching result
references. Thirty select used binders. Two stronger kernel examples prove
full Value equality from their own actual closed source construction. One
selects an open inner used Mu and replaces its self with a captured outer
name. These cases are not a general reconstruction theorem.

## Main next proof

Prove retained-used Mu reconstruction congruence through actual selected
first-writer paths. Either establish equality of the two actual sequential
reconstructions or derive full open observations and ordered child origins.
Do not compare one reconstructed result with an unreconstructed ordinary
probe: the preserved raw-inner cleanup counterexample refutes that claim.

Use StoredReconstructionReplay.mu for actual call completion and common-final
replay. Use GrowthExecution.closed_path or build_path for causal growth.
Use GrowthWriters.from_empty for the selected original writer. Its
Written.raw_callbacks gives both original raw calls and growth into the
same reader. These results do not supply the missing congruence law.

Plan equivalence compares the same original stored value across capture
layouts. It does not compare distinct raw callback values. The old unused
Mu comparison does not cover a retained-used Mu. The open observation
relation preserves bare names because row-only equivalence is insufficient.

Freshness must concern live fixed captures. Ordinary and reserved markers
have actual creation-time freshness producers. Depth can alias captures.
Replacement values may intentionally alias markers and captured names.
Do not add an unsupported fresh-replacement premise. Four-table Grows does
not supply issued-reference extension. Derive that separately where needed.
Open observations use one fixed view. Prove transport before changing it.

Then compose recursive row provenance with current native callbacks and
protected edge histories on the same trace. General outer-node progress,
nonempty live walks, full mutual completion, repeated-pass convergence,
current frontend/error adapters, concrete runtime effects, and complete
public Haskell correspondence remain open. Do not narrow the whole goal to
the current reconstruction subproblem.

## Preservation and publication

All prior proof, counterexample, repair, draft, and evidence bytes are retained.
The backup is codex/backup-retained-mu-reconstruction-20261017-2001.
The starting baseline has 19082 tracked files, 3088 older non-Audit Lean
sources, 242 Haskell files, 206 active-package files, two stashes, and three
other worktrees. The preservation verifier checks 109 frozen module
manifests with 852 hash references, including this checkpoint.

Four component manifests verify 181 file hash references. The root manifests
and SHA256SUMS cover the remaining proof probes and checkpoint files. After
publication, use verify-closure.py with a fresh remote readback. Save closure
output outside this frozen directory. Start a new directory for later work.

Use heavy-management for heavy work. Check /tmp/mcfta-weekly-usage.py before
the next sustained run. Stop owned work at one percent remaining. Do not
interpret a stale or missing budget reading as permission. Push only the
formalize branch under the existing authorization. Preserve the optimized
interned core and every earlier source artifact.

No Haskell patch or new production defect was added. Field-pool repair
b9219b9e remains merged and validated. FINDINGS keeps its reproducer, paths,
commit, checks, and status before historical reports. Record each later
Haskell repair there for external work. No board post is authorized here.
