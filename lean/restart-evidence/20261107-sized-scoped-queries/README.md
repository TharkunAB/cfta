# Exact guarded queries after scoped erasure

The source is `lean/MicroCFTA/SourceSizedScopedQueries.lean`.
SHA256: `c424ade8af54e0320809e351f96f1d3c855b39d9da7aad21d570e01757619046`.

`checked.json` records 2 checked public laws. The actual Lake target
and this source passed with Lean 4.34.1 in `shell.nix`. The source and axiom
report used `-j1` and warnings as errors. Only `propext`, `Classical.choice`,
and `Quot.sound` are allowed. This packet does not establish a cold full build,
Haskell execution, native storage, or total work bounds. Read the source
module comment for its exact scope.

Run this command from the repository root. Keep heavy checks serial.
The checker removes its temporary source and axiom report. It does not copy
the repository or a build tree.

```sh
env XDG_RUNTIME_DIR=/run/user/1000 \
  DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  CAPPED_UNIT=mcfta-sized-scoped-queries-recheck \
  HEAVY_PEAKS=/tmp/mcfta-sized-routing-recheck-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 \
  python3 lean/restart-evidence/20261107-sized-scoped-queries/check.py
```

The checker prints a fresh JSON report. Compare its source hash and axiom
entries with `checked.json`. The archived report is the successful observed
result. Earlier failed drafts remain marked in the runtime handoff.
