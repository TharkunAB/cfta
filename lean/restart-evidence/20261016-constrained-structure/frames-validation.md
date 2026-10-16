# Checked native frame validation

Recorded: 2026-10-16T16:19:20+02:00.

`SourceCurrentAllocatedFiniteOrdinaryFrames.lean` is frozen at SHA256
`88e898cf7045e25f8c787a8ce6c75a2c511f6373cbecde5905de90727dc9b279`. The file has 84 lines.

The direct source check exited 0. Its raw log is `frames-direct-1.log`.
The parent canonical build exited 0 with 1104 jobs. Its raw log is
`frames-build-1.log`. That build replayed the existing unused `inputs`
warning in `InternedFreshOrdinaryClosedCompletion.lean`. The new module
has no warnings.

The final imported public probe exited 0. It checks four public axioms and
four complete signatures. The imported integration probe exited 0. It checks
two kernel theorems and both complete signatures. Each axiom report contains
only `propext`, `Classical.choice`, and `Quot.sound`. Neither imported log
contains warnings, errors, or `sorryAx`.

Commands from the repository root:

```sh
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryFrames.lean > lean/restart-evidence/20261016-constrained-structure/frames-direct-1.log 2>&1
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-constrained-structure/frames-public.lean > lean/restart-evidence/20261016-constrained-structure/frames-public-imported.log 2>&1
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-constrained-structure/frames-kernels.lean > lean/restart-evidence/20261016-constrained-structure/frames-kernels-imported.log 2>&1
```

The parent ran the canonical Lake target. This task ran no Lake command.
No owned process remains active. The evidence contains no compiled artifacts.
The source snapshot is `frames-source.lean`. The prefix probes retain the
initial direct checks before the canonical module was available.
