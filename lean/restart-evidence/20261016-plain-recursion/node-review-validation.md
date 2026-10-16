# Independent plain-node validation

Recorded at 2026-10-16T15:55:27+02:00.

Root-owned `node-build-1.log` reports successful canonical completion with 1512 jobs. Parent observed terminal exit 0. Its only warning is the historical unused `inputs` warning in InternedFreshOrdinaryClosedCompletion. Final Node SHA256: `f0215ebd5409c623b1cdee268dcd098421ebd079d6e53709c1c6269ac6979164`.

Independent imported checks both reached terminal exit 0 on the first attempt:

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-plain-recursion/node-review-public.lean > lean/restart-evidence/20261016-plain-recursion/node-review-public.log 2>&1
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-plain-recursion/node-review-kernels.lean > lean/restart-evidence/20261016-plain-recursion/node-review-kernels-1.log 2>&1
```

One public full-signature/axiom pair and four integration-kernel signature/axiom pairs passed. All five reports use only propext, Classical.choice, and Quot.sound. Neither direct log contains a warning, error, or sorryAx. No compiled artifact was generated in the evidence directory.

The final history map links original Rows886333, intermediate reviewed Rowsa128, final Rowsce1, and the exact reviewed Node58ae snapshot to final Nodef021. Reconstruction of Rows886333 was accepted only after its bytes matched the previously recorded SHA256. Frozen historical manifests and snapshots were not changed.
