# Recursive event source-read checkpoint

Proof commit: `776875701`. Start: `8282cca55`.
Main: `184bba662`. Upstream merge: `a3cf692cb`.

Read `lean/notes-current-recursive-event-source-read.md` for the contract.
Read root FINDINGS for Haskell repair handoffs. This checkpoint adds no
local Haskell behavior patch. The upstream import changes six earlier
Haskell files and adds one Haskell file. The other 261 remain unchanged.
The new implementation paths have explicit correspondence gaps.

Three production modules expose nine public declarations. Five selected
full groups check these declarations and two constructed theorems.
Three production and two constructed strict logs are empty. The exact
default full Audit is full-audit-1. Root observed execution handle 15491
return exit zero: 3459 jobs and 73817 axiom dependency checks. The sole
warning is the older unused inputs binding.

The 23 raw logs include 21 entered Lean jobs and two blocked wrappers.
Both wrappers failed before Lean started. Failed elaboration attempts
retain their original names. The path fixture also retains a rejected
packaging check. Its final packaging uses the separate path-kernels-final
files. No rejected attempt is selected as passing evidence.
Selected runs have effective 4 GiB maximum/high limits and zero swap.
Each owner retains an immutable peak snapshot.

Eight component manifests pin sources, probes, logs, limits and reviews.
The source review and current document review have separate exact pins.
The next edge-writer handoff records a proposed proof, with no new Lean job.
Root-scope pins connect the current claims to their theorem sources.
Upstream-refresh pins all twelve upstream paths. SHA256SUMS covers every
evidence file except itself. Raw logs require explicit staging because
the repository ignores log files.

The whitespace policy classifies retained evidence bytes. The production
and current-document whitespace check passes. Raw evidence is unchanged.

From the repository root, run:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 lean/restart-evidence/20261019-recursive-event-source-read/verify-checkpoint.py
PYTHONDONTWRITEBYTECODE=1 python3 lean/restart-evidence/20261019-recursive-event-source-read/verify-preservation.py
PYTHONDONTWRITEBYTECODE=1 python3 lean/restart-evidence/20261019-recursive-event-source-read/verify-closure.py
```

Closure requires a committed clean worktree. It compares tracked bytes and
modes with the index and HEAD. It requires every evidence file to be
tracked. It rechecks the retained checkpoint and preservation reports.
The publication block in NEXT-PROMPT remains in force. These commands
perform no publication or board write.
