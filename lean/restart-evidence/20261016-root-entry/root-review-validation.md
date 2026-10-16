# Independent root-entry validation

Validated at 2026-10-16 15:06 CEST.

Commands ran from `/home/tritlo/Code/mcfta`:

```sh
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-root-entry/root-review-public.lean
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-root-entry/root-review-kernels.lean
```

Both final direct imported runs returned exit code 0. The public run checks both root endpoints with full explicit signatures and axiom reports. The kernel run checks four integration theorems. All six reports use only `propext`, `Classical.choice`, and `Quot.sound`. Neither final log contains a warning, error, or `sorryAx`. `root-review-results.json` records the actual direct process exit codes.

The source bytes match the final frozen hashes. Text copies are retained beside this note. The root-owned `root-build-1.log` records canonical success in 1494 jobs. The root-owned `audit-build-1.log` records aggregate success in 2477 jobs and 58771 theorem dependency checks. The aggregate has only the historical unused-input warning. This reviewer ran no Lake, Haskell, Git mutation, or board action and changed no proof module.

The independent source review is `root-review.md`. The initialization's separate public and kernel checks belong to required_memos in `init-*`. There are no compiled artifacts in this review's evidence. No owned process or build slot remains active.
