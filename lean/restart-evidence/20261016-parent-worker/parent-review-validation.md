# Parent worker independent validation

Timestamp: 2026-10-16 14:13 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedParentWorker.lean`.
SHA256: `cd54649ba473f2cf293bf359d7477e2d9059ed4777bd3c697fd702b285c129fa`.

Imported direct Lean checks both terminate with exit 0:

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-parent-worker/parent-public.lean > lean/restart-evidence/20261016-parent-worker/parent-public-1.log 2>&1
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-parent-worker/parent-kernels.lean > lean/restart-evidence/20261016-parent-worker/parent-kernels-1.log 2>&1
```

Four public axiom/full-signature pairs and seven kernel examples pass. No warnings appear. Foundations are limited to propext, Classical.choice, and Quot.sound. No compiled evidence artifact is produced. No active process or canonical build slot is held. Root owns canonical builds and all repository mutations.

See `parent-review.md` for source scope and kernel coverage. `outer-worker-plan.md` is a read-only next-step recommendation, not an implementation or completed outer-termination proof. `outer-worker-source-hashes.json` records the exact live source used for that recommendation.
