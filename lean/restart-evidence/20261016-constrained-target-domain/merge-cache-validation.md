# Finite ordinary merge-cache validation

Recorded: 2026-10-16T16:41:31+02:00.

Frozen source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryMergeCache.lean`.
It has 72 lines and SHA256 `2bbf781ac0a2adec332214d5c3f57d56552308a6ae4dbd9ae94e14d66f5e6bf4`.

The direct source check exited 0 without warnings (`merge-cache-direct-1.log`).
The parent canonical target exited 0 with 1024 jobs (`merge-cache-build-1.log`).
It replayed only the historical unused `inputs` warning. This task ran no Lake.

Final imported public probe: exit 0, five axiom checks and five complete
signatures. `empty_stored` is axiom-free. Other declarations use only `propext`
and `Quot.sound`. Final imported integration probe: exit 0, four kernel checks
and four complete signatures. Neither final log has warnings, errors, or
`sorryAx`.

The first kernel probe failed on an ambiguous `.empty` in the external Empty
miss construction. The second supplies its value type and passes. The failed
raw log remains `merge-cache-kernels-1.log`. No source theorem changed.

Commands from the repository root:

```sh
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryMergeCache.lean > lean/restart-evidence/20261016-constrained-target-domain/merge-cache-direct-1.log 2>&1
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-constrained-target-domain/merge-cache-public.lean > lean/restart-evidence/20261016-constrained-target-domain/merge-cache-public-1.log 2>&1
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-constrained-target-domain/merge-cache-kernels.lean > lean/restart-evidence/20261016-constrained-target-domain/merge-cache-kernels-2.log 2>&1
```

The kernels compose physical and structural completion invariants, retain an
earlier winner without a candidate-domain premise, retain old entries across
two serial completions, and construct actual Empty miss/hit graphs. The last
kernel proves that a proposed reference candidate loses to the existing Empty
winner. No compiled artifact or owned active process remains in this evidence.
