# Finite ordinary literal merge-worker validation

Recorded: 2026-10-16T16:48:06+02:00.

Frozen source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryMergeWorker.lean`.
It has 54 lines and SHA256 `1c48c895be25022ef1eaff27700ce4d37a07eb83f3b1597367e3f31675b9ec4d`.

Direct source check: terminal exit 0, no warning (`merge-worker-direct-1.log`).
Parent canonical combined build: terminal exit 0, 1298 jobs
(`target-worker-build-1.log`). The new worker module built at job 1297. Only
the historical unused inputs warning was replayed. This task ran no Lake.

Imported public and integration probes each exited 0 with no warnings or errors.
There are two public axiom/full-signature pairs and two integration pairs.
All use only the permitted foundations propext, Classical.choice and Quot.sound.
The prefix integration probe also passed while the canonical dependency was
pending. It is retained separately. No failed compiler run occurred.

The first integration theorem derives the second supplied literal call's
initial Ready, physical/structural memo, availability and input domain from
its first actual return. The second constructs both literal completions with
no supplied success or graph premise. It threads the actual generated input,
physical state and warm memo and retains both larger-bound stability families.

Commands from the repository root:

```sh
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryMergeWorker.lean > lean/restart-evidence/20261016-constrained-target-domain/merge-worker-direct-1.log 2>&1
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-constrained-target-domain/merge-worker-public.lean > lean/restart-evidence/20261016-constrained-target-domain/merge-worker-public-1.log 2>&1
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-constrained-target-domain/merge-worker-kernels.lean > lean/restart-evidence/20261016-constrained-target-domain/merge-worker-kernels-1.log 2>&1
```

No owned process remains active. No compiled artifact was added to evidence.
