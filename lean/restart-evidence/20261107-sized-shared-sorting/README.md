# Shared canonical sorting across roots

The source is `lean/MicroCFTA/SourceSizedSharedSorting.lean`.
SHA256: `479c42cf94dd6c398845cb461a8767ffc0a51898dc74c4b7114f4f22f47a1cde`.

`checked.json` records 4 checked public laws. The actual Lake target
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
  CAPPED_UNIT=mcfta-sized-shared-sorting-recheck \
  HEAVY_PEAKS=/tmp/mcfta-sized-routing-recheck-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 \
  python3 lean/restart-evidence/20261107-sized-shared-sorting/check.py
```

The checker prints a fresh JSON report. Compare its source hash and axiom
entries with `checked.json`. The archived report is the successful observed
result. Earlier failed drafts remain marked in the runtime handoff.
