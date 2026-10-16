# Scan caller public validation

The parent reported canonical target success with 1297 jobs before these imported checks. This owner ran no Lake or Haskell command for the review.

Both direct commands returned exit 0:

```sh
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-typing-do-seeded-worker/scan-caller-public.lean
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-typing-do-seeded-worker/scan-caller-kernels.lean
```

`scan-caller-public-1.log` contains all six public axiom checks and all six complete signatures: Caller verified/actual/finite and WorkerActual sound/verified/finite. Only propext, Classical.choice, and Quot.sound occur, with printed universe annotations. There are no sorryAx, errors, or warnings. `scan-caller-kernels-1.log` is empty. Its three external examples prove serial two-scan context/inventory reuse, same-return strict/global/fourth receipts, and true-stop plus selected-failure state behavior. No compiled artifact or active process remains.
