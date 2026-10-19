# Recursive event observation checkpoint

Proof commit: `d153d37d7`. Start: `60403eced`.
Main: `b45051e3e`. Upstream merge: `fec741514`.

Read `lean/notes-current-recursive-event-observation.md` for the contract.
Read root `FINDINGS.md` for Haskell repair handoffs. This checkpoint adds
no local Haskell repair. The upstream import adds Specftacular packages.

`new-modules.json` and `frozen-modules.json` identify five production modules.
`public-heads.json` lists all ten public declarations. Seven selected full
groups check those declarations and two constructed theorems. Five
production strict logs and two constructed strict logs are empty.

The exact default build is `full-audit-1`. Root observed execution handle
23491 return exit zero. It built 3456 jobs and checked 73793 axiom
dependencies. The sole warning is the previous unused `inputs` binding.

The 33 raw logs include 32 entered Lean jobs and one blocked wrapper.
The wrapper failed before Lean started. Failed elaboration attempts remain
under their original attempt names. Selected runs have effective 4 GiB
maximum/high limits and zero swap. Each owner retains an immutable peak
snapshot. No selected result depends on a missing cgroup-limits receipt.

Component manifests pin the owned source, probes, logs, limits and reviews.
The source review and current document review have separate exact pins.
`root-scope-manifest.json` pins current claims and their theorem sources.
`upstream-refresh.json` pins all 53 upstream paths and lists all additions.
`SHA256SUMS` covers every evidence file except itself. Raw logs are tracked
explicitly because the repository ignore rules exclude log files.

`whitespace-policy.json` classifies blank final lines in retained evidence.
The production and current-document whitespace check passes. Raw evidence
bytes are preserved.

From the repository root, run:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 lean/restart-evidence/20261019-recursive-event-observation/verify-checkpoint.py
PYTHONDONTWRITEBYTECODE=1 python3 lean/restart-evidence/20261019-recursive-event-observation/verify-preservation.py
PYTHONDONTWRITEBYTECODE=1 python3 lean/restart-evidence/20261019-recursive-event-observation/verify-closure.py
```

Closure requires a committed clean worktree. It compares tracked file bytes
and modes with both the index and HEAD. It checks all evidence files are
tracked. It rechecks the retained checkpoint and preservation reports.
The publication block in NEXT-PROMPT remains in force. These commands
perform no publication or board write.
