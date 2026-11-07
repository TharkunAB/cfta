# Computed shared determinization at limit 1024

The source is `lean/MicroCFTA/SourceSizedGuardedDeterminization.lean`.
SHA256: `5fb62e2ba76a8af6e799e79fc7513fe6116122bedbb07ad8288e4bc1fdd281dd`.

`checked.json` records 3 checked public laws. The actual Lake target
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
  CAPPED_UNIT=mcfta-sized-guarded-determinization-recheck \
  HEAVY_PEAKS=/tmp/mcfta-sized-routing-recheck-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 \
  python3 lean/restart-evidence/20261107-sized-guarded-determinization/check.py
```

The checker prints a fresh JSON report. Compare its source hash and axiom
entries with `checked.json`. The archived report is the successful observed
result. Earlier failed drafts remain marked in the runtime handoff.
